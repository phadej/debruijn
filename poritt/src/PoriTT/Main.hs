module PoriTT.Main (
    main,
    batchFile,
    Environment,
    builtinEnvironment,
) where

import Control.Monad.Trans.Class        (lift)
import Control.Monad.Trans.State.Strict (StateT (StateT), evalStateT, execStateT, get, put)
import System.Console.ANSI              (hSupportsANSIColor)
import System.Directory                 (canonicalizePath)
import System.Exit                      (exitFailure)
import System.FilePath                  (takeDirectory)
import System.IO                        (Handle, hPutStrLn, stdout)

import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import qualified System.FilePath as FP
import qualified Text.Parsec     as P

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Elab
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Info
import PoriTT.Lexer
import PoriTT.Lint
import PoriTT.Macro
import PoriTT.Name
import PoriTT.Opts
import PoriTT.Parser
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Raw
import PoriTT.Rename
import PoriTT.Simpl
import PoriTT.Term
import PoriTT.Value
import PoriTT.Well

modifyM :: Monad m => (s -> m s) -> StateT s m ()
modifyM f = StateT $ \ s -> do
    s' <- f s
    return ((), s')

data Environment = Environment
    { envHandle   :: Handle
    , envColour   :: Bool
    , envGlobals  :: Map Name Global
    , envMacros   :: Map Name Macro
    , envIncluded :: Set FilePath
    }

builtinEnvironment :: Handle -> IO Environment
builtinEnvironment hdl = do
    colour <- hSupportsANSIColor hdl
    return Environment
        { envHandle = hdl
        , envColour = colour
        , envGlobals = Map.fromList $ map (\g -> (gblName g, g))
            [ evalDescGlobal
            , allTypeGlobal
            , allTermGlobal
            ]
        , envMacros = Map.empty
        , envIncluded = Set.empty
        }

nameScopeFromEnv :: Environment -> NameScope
nameScopeFromEnv Environment {..} =
    nameScopeFromSet (Map.keysSet envGlobals) <> nameScopeFromSet (Map.keysSet envMacros)

readStatements :: FilePath -> StateT Environment IO [Stmt]
readStatements fn = do
    cfn <- lift (canonicalizePath fn)
    env <- get
    if Set.member cfn env.envIncluded
    then return [DoneStmt fn]
    else do
        -- mark as included
        put $ env { envIncluded = Set.insert cfn env.envIncluded }

        -- read file
        bs <- lift $ BS.readFile fn

        -- parse statements
        statements' <- either (printError . ppStr . show) return $
            P.parse (many stmtP <* eofP) fn (initLexerState fn bs)

        let statements = statements' ++ [DoneStmt fn]

        -- recurse on include stmts.
        fmap concat $ for statements $ \stmt -> case stmt of
            IncludeStmt fn' -> fmap (stmt :) $ readStatements (takeDirectory fn FP.</> fn')
            _               -> return [stmt]

batchFile
    :: Opts                  -- ^ options
    -> FilePath              -- ^ input file
    -> Environment             -- ^ evaluation state
    -> IO (Environment)        -- ^ new evaluation state
batchFile opts fn = execStateT $ do
    statements <- readStatements fn

    for_ statements $ \s -> do
        stmt s
        printDoc ""
  where
    pipeline :: Raw -> StateT Environment IO (Elim EmptyCtx, VTerm EmptyCtx)
    pipeline e = do
        s <- get
        let names = nameScopeFromEnv s

        when (dumpPs opts) $ printDoc $ ppSoftHanging (ppAnnotate ACmd "ps") [ prettyRaw 0 e ]

        -- resolve names: rename
        w <- either (printErrors . fmap ppStr) return $ resolve (emptyRenameCtx (envGlobals s) (envMacros s)) e

        when (dumpRn opts) $  printDoc $ ppSoftHanging (ppAnnotate ACmd "rn") [ prettyWell names EmptyEnv 0 w ]

        -- elaborate, i.e. type-check
        (e1, et) <- either (printError . ppStr) return $ infer (emptyElabCtx names) w

        when (dumpTc opts) $ printDoc $ ppSoftHanging (ppAnnotate ACmd "tc") [ prettyElim names EmptyEnv 0 e1 ]

        -- check that we elaborated correctly
        et1 <- either (printError . ppStr) return $ lintInfer (emptyLintCtx names) e1
        case (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names) VUni et et1) of
            Right _   -> pure ()
            Left msg -> printError $ ppVCat
                [ "First lint pass returned different types"
                , msg
                , "*" <+> prettyVTermZ UnfoldNone names et
                , "*" <+> prettyVTermZ UnfoldNone names et1
                ]

        -- TODO: stage type.

        e2 <- either (printError . ppStr . show) return $ preElim SZ EmptyEnv e1
        when (dumpSt opts) $ printDoc $ ppSoftHanging (ppAnnotate ACmd "st") [ prettyElim names EmptyEnv 0 e2 ]

        et2 <- either (printError . ppStr) return $ lintInfer (emptyLintCtx names) e2
        case (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names) VUni et et2) of
            Right _   -> pure ()
            Left msg -> printError $ ppVCat
                [ "Second lint pass returned different types"
                , msg
                , "*" <+> prettyVTermZ UnfoldNone names et
                , "*" <+> prettyVTermZ UnfoldNone names et1
                ]


        -- few loops of simplifier
        e3 <- simplLoop "s1" e2 et
        e4 <- simplLoop "s2" e3 et
        e5 <- simplLoop "s3" e4 et

        return (e5, et)

    simplLoop :: Doc -> Elim EmptyCtx -> VTerm EmptyCtx -> StateT Environment IO (Elim EmptyCtx)
    simplLoop iter e et = do
        s <- get
        let names = nameScopeFromEnv s

        let e' = simplElim SZ emptySub e

        -- check that we simplified correctly
        et' <- either (printError . ppStr) return $ lintInfer (emptyLintCtx names) e
        case (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names) VUni et et') of
            Right _   -> pure ()
            Left msg -> printError $ ppVCat
                [ "Simplify lint pass returned different types"
                , msg
                , "*" <+> prettyVTermZ UnfoldNone names et
                , "*" <+> prettyVTermZ UnfoldNone names et'
                ]

        when (dumpSimpl opts) $ printDoc $ ppSoftHanging (ppAnnotate ACmd iter) [ prettyElim names EmptyEnv 0 e' ]

        return e'

    stmt :: Stmt -> StateT Environment IO ()
    stmt (DefineStmt name e) = do
        when (optsEcho opts) $ printDoc $ ppSoftHanging
            (ppAnnotate ACmd "define" <+> prettyName name)
            [ "=" <+> prettyRaw 0 e
            ]

        s <- get
        let names = nameScopeFromEnv s

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        (e', et) <- pipeline e

        let ev = evalElim SZ emptyEvalEnv e'
        let g :: Global
            g = Global
                { gblName   = name
                , gblTerm   = e'
                , gblType   = et
                , gblVal    = ev
                , gblInline = False
                }

        put $ s { envGlobals = Map.insert name g (envGlobals s) }

        printDoc $ ppSoftHanging
            (ppAnnotate ACmd "defined" <+> prettyName name)
            [ ":" <+> prettyVTermZ UnfoldNone names et
            , "=" <+> case e' of
                Ann t _ -> prettyTerm names EmptyEnv 0 t
                _       -> prettyElim names EmptyEnv 0 e'
            ]

    stmt (DefineStmt' name ty t) = do
        when (optsEcho opts) $ printDoc $ ppSoftHanging
            (ppAnnotate ACmd "define" <+> prettyName name)
            [ ":" <+> prettyRaw 0 ty
            , "=" <+> prettyRaw 0 t
            ]

        s <- get
        let names = nameScopeFromEnv s

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        (e', et) <- pipeline (RAnn t ty)

        let ev = evalElim SZ emptyEvalEnv e'
        let g :: Global
            g = Global
                { gblName   = name
                , gblTerm   = e'
                , gblType   = et
                , gblVal    = ev
                , gblInline = False
                }

        put $ s { envGlobals = Map.insert name g (envGlobals s) }

        printDoc $ ppSoftHanging
            (ppAnnotate ACmd "defined" <+> prettyName name)
            [ ":" <+> prettyVTermZ UnfoldNone names et
            , "=" <+> case e' of
                Ann t' _ -> prettyTerm names EmptyEnv 0 t'
                _        -> prettyElim names EmptyEnv 0 e'
            ]

    stmt (MacroStmt name xs0 t) = do
        when (optsEcho opts) $ printDoc $ ppSoftHanging
            (ppAnnotate ACmd "macro" <+> prettyName name)
            [ "=" <+> prettyRaw 0 t
            ]

        s <- get
        let names = nameScopeFromEnv s

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        let loop :: Env arity Name -> RenameCtx arity -> [Name] -> StateT Environment IO Macro
            loop ns ctx [] = do
                w <- either (printErrors . fmap ppStr) return $ resolve ctx t
                return (Macro name ns w)
            loop ns ctx (x:xs) = loop (ns :> x) (bindRenameCtx ctx (Just x)) xs

        m <- loop EmptyEnv (emptyRenameCtx (envGlobals s) (envMacros s)) xs0

        put $ s { envMacros = Map.insert name m (envMacros s) }

        printDoc $ infoMacro m

    stmt (TypeStmt e) = do
        s <- get
        let names = nameScopeFromEnv s

        (_e', et) <- pipeline e

        if optsEcho opts
        then do
            printDoc $
                ppAnnotate ACmd "type" <+> prettyRaw 0 e

            printDoc $ "  " <> ppSep
                [ ":" <+> prettyVTermZ UnfoldNone names et
                ]

        else printDoc $ ":" <+> prettyVTermZ UnfoldNone names et

    stmt (EvalStmt e) = do
        s <- get
        let names = nameScopeFromEnv s

        (e', et) <- pipeline e

        let u :: Unfold
            u = if optsEvalFull opts then UnfoldAll else UnfoldElim

        if optsEcho opts
        then do
            printDoc $ ppSoftHanging
                (ppAnnotate ACmd "eval" <+> prettyRaw 0 e)
                [ "=" <+> prettyVElimZ u names (evalElim SZ emptyEvalEnv e')
                , ":" <+> prettyVTermZ UnfoldNone names et
                ]

        else printDoc $ "=" <+> prettyVElimZ u names (evalElim SZ emptyEvalEnv e')

    stmt (InfoStmt x) = do
        when (optsEcho opts) $ printDoc $
            ppAnnotate ACmd "info" <+> prettyName x

        Environment _ _ globals macros _ <- get

        if | Just g <- Map.lookup x globals -> printDoc $ infoGlobal g
           | Just m <- Map.lookup x macros  -> printDoc $ infoMacro m
           | otherwise -> printError $ prettyName x <+> "is unknown"

    stmt (InlineStmt x) = do
        when (optsEcho opts) $ printDoc $
            ppAnnotate ACmd "inline" <+> prettyName x

        env@(Environment _ _ globals _ _) <- get

        if | Map.member x globals -> put $ env { envGlobals = Map.adjust (\g -> g { gblInline = True }) x globals }
           | otherwise -> printError $ prettyName x <+> "is unknown"

    stmt (SectionStmt title) = do
        when (optsEcho opts) $ printDoc $
            ppAnnotate ACmd "section" <+> ppText title

    stmt (IncludeStmt fp) = do
        when (optsEcho opts) $ printDoc $
            ppAnnotate ACmd "include" <+> prettyFilePath fp

    stmt (DoneStmt fp) = do
        when (optsEcho opts) $ printDoc $
            ppAnnotate ACmd "end-of-file" <+> prettyFilePath fp

main :: IO ()
main = do
    (opts, args) <- parseOpts
    env <- builtinEnvironment stdout
    evalStateT (mapM_ (\arg -> modifyM (batchFile opts arg)) args) env

prettyVTermZ :: Unfold -> NameScope -> VTerm EmptyCtx -> Doc
prettyVTermZ unfold ns v = case quoteTerm unfold SZ v of
    Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyTerm ns EmptyEnv 0 n

prettyVElimZ :: Unfold -> NameScope -> VElim EmptyCtx -> Doc
prettyVElimZ unfold ns v = case quoteElim unfold SZ v of
    Left err        -> ppStr (show err)           -- This shouldn't happen if type-checker is correct.
    Right (Ann t _) -> prettyTerm ns EmptyEnv 0 t  -- don't print annotation second time.
    Right e         -> prettyElim ns EmptyEnv 0 e

printDoc :: Doc -> StateT Environment IO ()
printDoc d = do
    Environment { envHandle = hdl, envColour = colour } <- get
    let s = ppRender colour d
    lift $ hPutStrLn hdl s

printErrors :: Foldable f => f Doc -> StateT Environment IO a
printErrors msgs = do
    for_ msgs $ \msg -> printDoc $ ppAnnotate AErr "Error:" <+> msg
    lift exitFailure

printError :: Doc -> StateT Environment IO a
printError msg = do
    printDoc $ ppAnnotate AErr "Error:" <+> msg
    lift exitFailure
