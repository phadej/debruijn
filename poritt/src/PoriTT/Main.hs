module PoriTT.Main (
    main,
    batchFile,
    Environment,
    builtinEnvironment,
) where

import Control.Monad.Trans.Class        (lift)
import Control.Monad.Trans.State.Strict (StateT (StateT), evalStateT, execStateT, get, put)
import System.Console.ANSI              (hSupportsANSIColor)
import System.Environment               (getArgs)
import System.Exit                      (exitFailure)
import System.IO                        (Handle, hPutStrLn, stdout)

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

import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Text.Parsec     as P

modifyM :: Monad m => (s -> m s) -> StateT s m ()
modifyM f = StateT $ \ s -> do
    s' <- f s
    return ((), s')

data Environment = Environment
    { envGlobals :: Map Name Global
    , envMacros  :: Map Name Macro
    }

builtinEnvironment :: Environment
builtinEnvironment = Environment
    { envGlobals = Map.fromList $ map (\g -> (gblName g, g))
        [ evalDescGlobal
        , allTypeGlobal
        , allTermGlobal
        ]
    , envMacros = Map.empty
    }

nameScopeFromEnv :: Environment -> NameScope
nameScopeFromEnv (Environment g m) =
    nameScopeFromSet (Map.keysSet g) <> nameScopeFromSet (Map.keysSet m)

batchFile
    :: Opts                  -- ^ options
    -> FilePath              -- ^ input file
    -> Handle                -- ^ output handle
    -> Environment             -- ^ evaluation state
    -> IO (Environment)        -- ^ new evaluation state

batchFile opts fn hdl = execStateT $ do
    -- read file
    bs <- lift $ BS.readFile fn

    -- parse statements
    statements <- either (printError hdl . show) return $
        P.parse (many stmtP <* eofP) fn (initLexerState fn bs)

    mapM_ stmt statements
  where
    pipeline :: Raw -> StateT Environment IO (Elim EmptyCtx, VTerm EmptyCtx)
    pipeline e = do
        s <- get
        let names = nameScopeFromEnv s

        -- resolve names: rename
        w <- either (printErrors hdl) return $ resolve (emptyRenameCtx (envGlobals s) (envMacros s)) e

        -- elaborate, i.e. type-check
        (e1, et) <- either (printError hdl) return $ infer (emptyElabCtx names) w

        colour <- lift $ hSupportsANSIColor hdl

        -- check that we elaborated correctly
        et1 <- either (printError hdl) return $ lintInfer (emptyLintCtx names) e1
        case (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names) VUni et et1) of
            Right _   -> pure ()
            Left msg -> printError hdl $ ppRender colour $ ppVCat
                [ "First lint pass returned different types"
                , msg
                , "*" <+> prettyVTermZ UnfoldNone names et
                , "*" <+> prettyVTermZ UnfoldNone names et1
                ]

        -- few loops of simplifier
        e2 <- simplLoop e1 et
        e3 <- simplLoop e2 et
        e4 <- simplLoop e3 et
        e5 <- simplLoop e4 et

        return (e5, et)

    simplLoop :: Elim EmptyCtx -> VTerm EmptyCtx -> StateT Environment IO (Elim EmptyCtx)
    simplLoop e et = do
        s <- get
        let names = nameScopeFromEnv s
        colour <- lift $ hSupportsANSIColor hdl

        let e' = simplElim SZ emptySub e

        -- check that we simplified correctly
        et' <- either (printError hdl) return $ lintInfer (emptyLintCtx names) e
        case (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names) VUni et et') of
            Right _   -> pure ()
            Left msg -> printError hdl $ ppRender colour $ ppVCat
                [ "Second lint pass returned different types"
                , msg
                , "*" <+> prettyVTermZ UnfoldNone names et
                , "*" <+> prettyVTermZ UnfoldNone names et'
                ]

        return e'

    stmt :: Stmt -> StateT Environment IO ()
    stmt (DefineStmt name e) = do
        s <- get
        let names = nameScopeFromEnv s

        when (nameScopeMember name names) $
            printError hdl $ show $ prettyName name <+> "is already defined"

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

        colour <- lift $ hSupportsANSIColor hdl

        when (optsEcho opts) $ lift $ hPutStrLn hdl $ ppRender colour $ ppSoftHanging
            (ppAnnotate ACmd "define" <+> prettyName name)
            [ "=" <+> prettyRaw 0 e
            ]

        lift $ hPutStrLn hdl $ ppRender colour $ ppSoftHanging
            (ppAnnotate ACmd "defined" <+> prettyName name)
            [ ":" <+> prettyVTermZ UnfoldNone names et
            , "=" <+> case e' of
                Ann t _ -> prettyTerm names EmptyEnv 0 t
                _       -> prettyElim names EmptyEnv 0 e'
            ]

    stmt (DefineStmt' name ty t) = do
        s <- get
        let names = nameScopeFromEnv s

        when (nameScopeMember name names) $
            printError hdl $ show $ prettyName name <+> "is already defined"

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

        colour <- lift $ hSupportsANSIColor hdl

        when (optsEcho opts) $ lift $ hPutStrLn hdl $ ppRender colour $ ppSoftHanging
            (ppAnnotate ACmd "define" <+> prettyName name)
            [ ":" <+> prettyRaw 0 ty
            , "=" <+> prettyRaw 0 t
            ]

        lift $ hPutStrLn hdl $ ppRender colour $ ppSoftHanging
            (ppAnnotate ACmd "defined" <+> prettyName name)
            [ ":" <+> prettyVTermZ UnfoldNone names et
            , "=" <+> case e' of
                Ann t' _ -> prettyTerm names EmptyEnv 0 t'
                _        -> prettyElim names EmptyEnv 0 e'
            ]

    stmt (MacroStmt name xs0 t) = do
        s <- get
        let names = nameScopeFromEnv s

        when (nameScopeMember name names) $
            printError hdl $ show $ prettyName name <+> "is already defined"

        let loop :: Env arity Name -> RenameCtx arity -> [Name] -> StateT Environment IO Macro
            loop ns ctx [] = do
                w <- either (printErrors hdl) return $ resolve ctx t
                return (Macro name ns w)
            loop ns ctx (x:xs) = loop (ns :> x) (bindRenameCtx ctx (Just x)) xs

        m <- loop EmptyEnv (emptyRenameCtx (envGlobals s) (envMacros s)) xs0

        put $ s { envMacros = Map.insert name m (envMacros s) }

        colour <- lift $ hSupportsANSIColor hdl

        when (optsEcho opts) $ lift $ hPutStrLn hdl $ ppRender colour $ ppSoftHanging
            (ppAnnotate ACmd "macro" <+> prettyName name)
            [ "=" <+> prettyRaw 0 t
            ]

        lift $ hPutStrLn hdl $ ppRender colour $ infoMacro m

    stmt (TypeStmt e) = do
        s <- get
        let names = nameScopeFromEnv s

        (_e', et) <- pipeline e

        colour <- lift $ hSupportsANSIColor hdl

        if optsEcho opts
        then do
            lift $ hPutStrLn hdl $ ppRender colour $
                ppAnnotate ACmd "type" <+> prettyRaw 0 e

            lift $ hPutStrLn hdl $ ppRender colour $ "  " <> ppSep
                [ ":" <+> prettyVTermZ UnfoldNone names et
                ]

        else lift $ hPutStrLn hdl $ ppRender colour $ ":" <+> prettyVTermZ UnfoldNone names et

    stmt (EvalStmt e) = do
        s <- get
        let names = nameScopeFromEnv s

        (e', et) <- pipeline e

        let u :: Unfold
            u = if optsEvalFull opts then UnfoldAll else UnfoldElim

        colour <- lift $ hSupportsANSIColor hdl

        if optsEcho opts
        then do
            lift $ hPutStrLn hdl $ ppRender colour $ ppSoftHanging
                (ppAnnotate ACmd "eval" <+> prettyRaw 0 e)
                [ "=" <+> prettyVElimZ u names (evalElim SZ emptyEvalEnv e')
                , ":" <+> prettyVTermZ UnfoldNone names et
                ]

        else lift $ hPutStrLn hdl $ ppRender colour $ "=" <+> prettyVElimZ u names (evalElim SZ emptyEvalEnv e')

    stmt (InfoStmt x) = do
        Environment globals macros <- get

        colour <- lift $ hSupportsANSIColor hdl

        when (optsEcho opts) $ lift $ hPutStrLn hdl $ ppRender colour $
            ppAnnotate ACmd "info" <+> prettyName x

        if | Just g <- Map.lookup x globals -> lift $ hPutStrLn hdl $ ppRender colour $ infoGlobal g
           | Just m <- Map.lookup x macros  -> lift $ hPutStrLn hdl $ ppRender colour $ infoMacro m
           | otherwise -> printError hdl $ show $ prettyName x <+> "is unknown"

    stmt (InlineStmt x) = do
        Environment globals m <- get

        colour <- lift $ hSupportsANSIColor hdl

        when (optsEcho opts) $ lift $ hPutStrLn hdl $ ppRender colour $
            ppAnnotate ACmd "inline" <+> prettyName x

        if | Map.member x globals -> put $ Environment (Map.adjust (\g -> g { gblInline = True }) x globals) m
           | otherwise -> printError hdl $ show $ prettyName x <+> "is unknown"

main :: IO ()
main = do
    args <- getArgs
    evalStateT (mapM_ (\arg -> modifyM (batchFile defaultOpts arg stdout)) args) builtinEnvironment

prettyVTermZ :: Unfold -> NameScope -> VTerm EmptyCtx -> Doc
prettyVTermZ unfold ns v = case quoteTerm unfold SZ v of
    Left err -> ppText (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyTerm ns EmptyEnv 0 n

prettyVElimZ :: Unfold -> NameScope -> VElim EmptyCtx -> Doc
prettyVElimZ unfold ns v = case quoteElim unfold SZ v of
    Left err        -> ppText (show err)           -- This shouldn't happen if type-checker is correct.
    Right (Ann t _) -> prettyTerm ns EmptyEnv 0 t  -- don't print annotation second time.
    Right e         -> prettyElim ns EmptyEnv 0 e

printErrors :: Foldable f => Handle -> f String -> StateT s IO a
printErrors hdl msgs = lift $ do
    -- TODO: some red color
    for_ msgs $ \msg -> hPutStrLn hdl $ "Error: " ++ msg
    exitFailure

printError :: Handle -> String -> StateT s IO a
printError hdl msg = lift $ do
    -- TODO: some red dcolour
    hPutStrLn hdl $ "Error: " ++ msg
    exitFailure
