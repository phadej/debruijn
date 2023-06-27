module PoriTT.Parser (
    Stmt (..),
    stmtP,
    eofP,
) where

import PoriTT.Base
import PoriTT.Lexer
import PoriTT.Loc
import PoriTT.Name
import PoriTT.Raw

import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import qualified Data.Text       as T
import qualified Text.Parsec     as P
import qualified Text.Parsec.Pos as P


-- | PoriTT statements
data Stmt
    = DefineStmt Name Raw       -- ^ define top level binding: @define foo = e@
    | DefineStmt' Name Raw Raw  -- ^ or @define bar : T = t@
    | EvalStmt Raw              -- ^ evaluate expression: @eval e@
    | TypeStmt Raw              -- ^ type-check expression: @type e@
    | InfoStmt Name             -- ^ information about a name: @info x@
    | InlineStmt Name           -- ^ mark binding to be inlined: @inline x@
    | MacroStmt Name [Name] Raw -- ^ define new macro: @macro bar x y z = t@
    | IncludeStmt FilePath      -- ^ include source file: @include "lib.ptt"@
    | SectionStmt Text          -- ^ section statement: @section "definitions"@
    | DoneStmt FilePath         -- ^ end-of-file
  deriving Show

type Parser = P.Parsec LexerState ()

stmtP :: Parser Stmt
stmtP = defineP <|> evalP <|> typeP <|> infoP <|> inlineP <|> macroP <|> includeP <|> sectionP

defineP :: Parser Stmt
defineP = do
    tokenP TkDefine
    name <- nameP
    alt1 name <|> alt2 name
  where
    alt1 name = do
        tokenP TkColon
        t <- rawP
        tokenP TkEquals
        s <- rawP
        return (DefineStmt' name t s)

    alt2 name = do
        tokenP TkEquals
        e  <- rawP
        return (DefineStmt name e)

evalP :: Parser Stmt
evalP = do
    tokenP TkEval
    e <- rawP
    return (EvalStmt e)

typeP :: Parser Stmt
typeP = do
    tokenP TkType
    e <- rawP
    return (TypeStmt e)

infoP :: Parser Stmt
infoP = do
    tokenP TkInfo
    x <- nameP
    return (InfoStmt x)

inlineP :: Parser Stmt
inlineP = do
    tokenP TkInline
    x <- nameP
    return (InlineStmt x)

macroP :: Parser Stmt
macroP = do
    tokenP TkMacro
    name <- nameP
    xs <- many nameP
    tokenP TkEquals
    s <- rawP
    return (MacroStmt name xs s)

includeP :: Parser Stmt
includeP = do
    tokenP TkInclude
    fp <- T.unpack <$> stringP
    return (IncludeStmt fp)

sectionP :: Parser Stmt
sectionP = do
    tokenP TkSection
    title <- stringP
    return (SectionStmt title)

tokenP :: Token -> Parser ()
tokenP t = P.token (showToken . snd) toPos (\(_, t') -> guard (t == t')) P.<?> showToken t

anyTokenP :: Parser Token
anyTokenP = P.token (showToken . snd) toPos (\(_, t) -> Just t)

eofP :: Parser ()
eofP = eof P.<?> "end of input" where
    eof = P.try $ (P.try anyTokenP >>= P.unexpected . showToken) <|> return ()

nameP :: Parser Name
nameP = p P.<?> "identifier" where
    p = P.token (showToken . snd) toPos $ \(_, t) -> case t of
        TkIdent n -> Just n
        _         -> Nothing

labelP :: Parser Label
labelP = p P.<?> "label" where
    p = P.token (showToken . snd) toPos $ \(_, t) -> case t of
        TkLabel n -> Just n
        _         -> Nothing

selectorP :: Parser Selector
selectorP = p P.<?> "selector" where
    p = P.token (showToken . snd) toPos $ \(_, t) -> case t of
        TkSelector n -> Just n
        _            -> Nothing

nameOrHoleP :: Parser Name
nameOrHoleP = nameP <|> holeName <$ tokenP TkHole

stringP :: Parser Text
stringP = p P.<?> "string literal" where
    p = P.token (showToken . snd) toPos $ \(_, t) -> case t of
        TkString l -> Just l
        _          -> Nothing


toPos :: (Loc, Token) -> P.SourcePos
toPos (Loc fn l c, _) = P.newPos fn l c

srcP :: Parser Raw -> Parser Raw
srcP p = do
    ls <- P.getInput
    rloc (lsLocation ls) <$> p
  where
    rloc l (RLoc _ x) = RLoc l x
    rloc l x          = RLoc l x

rawP :: Parser Raw
rawP = annP

annP :: Parser Raw
annP = srcP $ mkAnns <$> comP <*> many (tokenP TkColon *> comP) where
    mkAnns :: Raw -> [Raw] -> Raw
    mkAnns a bs = foldr1 RAnn (a :| bs)

comP :: Parser Raw
comP = srcP $ mkMuls <$> arrP <*> many (tokenP TkComma *> arrP) where
    mkMuls :: Raw -> [Raw] -> Raw
    mkMuls a bs = foldr1 RMul (a :| bs)

arrP :: Parser Raw
arrP = srcP $ mkArrs <$> astP <*> many (tokenP TkArrow *> astP) where
    mkArrs :: Raw -> [Raw] -> Raw
    mkArrs a bs = foldr1 RArr (a :| bs)

astP :: Parser Raw
astP = srcP $ mkArrs <$> appP <*> many (tokenP TkAst *> appP) where
    mkArrs :: Raw -> [Raw] -> Raw
    mkArrs a bs = foldr1 RPrd (a :| bs)

appP :: Parser Raw
appP = srcP $ P.choice
    [ RApp <$> atomP <*> many selectorOrAtomP
    , mkPie <$ tokenP TkForall    <*> some (pure (,) <$> tokenP TkLParen <*> some nameOrHoleP <* tokenP TkColon <*> rawP <* tokenP TkRParen) <* tokenP TkArrow <*> rawP
    , mkSgm <$ tokenP TkExists    <*> some (pure (,) <$> tokenP TkLParen <*> some nameOrHoleP <* tokenP TkColon <*> rawP <* tokenP TkRParen) <* tokenP TkAst <*> rawP
    , RSwh  <$ tokenP TkSwitch <*> atomP <*> atomP <*> between TkLBrace TkRBrace branchesP
    , tokenP TkDescS   >> many atomP >>= mkDeS
    , tokenP TkDescX   >> many atomP >>= mkDeX
    , tokenP TkDescInd >> many atomP >>= mkDeI
    , tokenP TkMu      >> many atomP >>= mkMuu
    , tokenP TkCon     >> many atomP >>= mkCon
    , tokenP TkInd     >> many atomP >>= mkInd
    , tokenP TkCode    >> many atomP >>= mkCod
    ]
  where
    mkPie :: [([Name], Raw)] -> Raw -> Raw
    mkPie xsa b = foldr (\(xs, a) t -> foldr (\x t' -> RPie x a t') t xs) b xsa

    mkSgm :: [([Name], Raw)] -> Raw -> Raw
    mkSgm xsa b = foldr (\(xs, a) t -> foldr (\x t' -> RSgm x a t') t xs) b xsa

    mkDeS :: [Raw] -> Parser Raw
    mkDeS [s,d] = pure $ RDeS s d
    mkDeS ts    = fail $ "`S expects two arguments, " ++ show (length ts) ++ " given"

    mkDeX :: [Raw] -> Parser Raw
    mkDeX [d] = pure $ RDeX d
    mkDeX ts  = fail $ "`X expects one argument, " ++ show (length ts) ++ " given"

    mkDeI :: [Raw] -> Parser Raw
    mkDeI [e,m,x,y,z] = pure $ RDeI e m x y z
    mkDeI ts          = fail $ "indDesc expects five arguments, " ++ show (length ts) ++ " given"

    mkMuu :: [Raw] -> Parser Raw
    mkMuu [t] = pure $ RMuu t
    mkMuu ts  = fail $ "mu expects one argument, " ++ show (length ts) ++ " given"

    mkCon :: [Raw] -> Parser Raw
    mkCon [t] = pure $ RCon t
    mkCon ts  = fail $ "con expects one argument, " ++ show (length ts) ++ " given"

    mkInd :: [Raw] -> Parser Raw
    mkInd [e,m,c] = pure $ RInd e m c
    mkInd ts      = fail $ "ind expects three arguments, " ++ show (length ts) ++ " given"

    mkCod :: [Raw] -> Parser Raw
    mkCod [a] = pure $ RCod a
    mkCod ts  = fail $ "Code expects one argument, " ++ show (length ts) ++ " given"

    branchesP :: Parser (Map Label Raw)
    branchesP = Map.fromList <$> P.sepBy branchP (tokenP TkSemi)

    branchP :: Parser (Label, Raw)
    branchP = (,) <$> labelP <* tokenP TkArrow <*> rawP


atomP :: Parser Raw
atomP = srcP $ P.choice
    [ RVar <$> nameP
    , RLbl <$> labelP
    , RUni <$ tokenP TkU
    , RDsc <$ tokenP TkDesc
    , RDe1 <$ tokenP TkDesc1
    , RHol <$ tokenP TkHole
    , between TkLParen TkRParen rawP
    , RFin . Set.fromList <$> between TkLBrace TkRBrace (many labelP)
    , mkLam <$ tokenP TkBackSlash <*> some nameOrHoleP <* tokenP TkArrow <*> rawP
    , RLet <$ tokenP TkLet <*> nameP <*> letDefP <* tokenP TkIn <*> rawP
    , RQuo <$> between TkLQuote TkRQuote rawP
    , RSpl <$ tokenP TkDollar <*> atomP
    ]
  where
    mkLam :: [Name] -> Raw -> Raw
    mkLam xs e = foldr RLam e xs

    letDefP :: Parser Raw
    letDefP = P.choice
        [ flip RAnn <$ tokenP TkColon <*> rawP <* tokenP TkEquals <*> rawP
        , tokenP TkEquals *> rawP
        ]

selectorOrAtomP :: Parser (Either Selector Raw)
selectorOrAtomP = Left <$> selectorP <|> Right <$> atomP

between :: Token -> Token -> Parser a -> Parser a
between l r p = tokenP l *> p <* tokenP r
