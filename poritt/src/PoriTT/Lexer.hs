{-# LANGUAGE TemplateHaskell #-}
module PoriTT.Lexer (
    Token (..),
    showToken,
    LexerState (..),
    initLexerState,
    scan,
) where

import Data.Char (isPrint)

import qualified Data.Text                as T
import qualified Data.Text.Encoding       as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Text.Parsec              as P

import PoriTT.Base
import PoriTT.Loc
import PoriTT.Name

-------------------------------------------------------------------------------
-- Tokens
-------------------------------------------------------------------------------

-- | Tokens produced by lexer.
data Token
    = TkIdent Name        -- ^ identifiers: @foobar@
    | TkLabel Label       -- ^ labels: @:label@
    | TkSelector Selector -- ^ selectors: @.fst@ or @.snd@
    | TkDefine            -- ^ keyword @define@
    | TkEval              -- ^ keyword @eval@
    | TkType              -- ^ keyword @type@
    | TkInfo              -- ^ keyword @info@
    | TkInline            -- ^ keyword @inline@
    | TkMacro             -- ^ keyword @macro@
    | TkLet               -- ^ keyword @let@
    | TkIn                -- ^ keyword @in@
    | TkU                 -- ^ keyword @U@
    | TkForall            -- ^ keyword @forall@
    | TkExists            -- ^ keyword @exists@
    | TkSwitch            -- ^ keyword @switch@
    | TkMu                -- ^ @mu@
    | TkInd               -- ^ @ind@
    | TkCon               -- ^ @con@
    | TkDesc              -- ^ @Desc@
    | TkDesc1             -- ^ @`1@
    | TkDescS             -- ^ @`S@
    | TkDescX             -- ^ @`X@
    | TkDescInd           -- ^ @indDesc@
    | TkCode              -- ^ @Code@
    | TkLParen            -- ^ left parenthesis: @(@
    | TkRParen            -- ^ right parenthesis: @)@
    | TkLBracket          -- ^ left parenthesis: @[@
    | TkRBracket          -- ^ right parenthesis: @]@
    | TkLBrace            -- ^ left parenthesis: @{@
    | TkRBrace            -- ^ right parenthesis: @}@
    | TkArrow             -- ^ arrow: @->@
    | TkBackSlash         -- ^ backslash: @\\@
    | TkColon             -- ^ colon: @:@
    | TkSemi              -- ^ semi: @;@
    | TkComma             -- ^ comma: @,@
    | TkAst               -- ^ ast: @*@
    | TkEquals            -- ^ equals: @=@
    | TkHole              -- ^ hole: @_@
    | TkTilde             -- ^ tilde: @~@
    | TkEOF               -- ^ end-of-file token
    | TkError String
  deriving (Eq)

showToken :: Token -> String
showToken (TkIdent n) = "identifier " ++ show (prettyName n)
showToken (TkLabel l) = "label " ++ show (prettyLabel l)
showToken (TkSelector s) = "selector " ++ show (prettySelector s)
showToken TkDefine    = "define"
showToken TkEval      = "eval"
showToken TkType      = "type"
showToken TkLet       = "let"
showToken TkIn        = "in"
showToken TkInfo      = "info"
showToken TkInline    = "inline"
showToken TkMacro     = "macro"
showToken TkU         = "U"
showToken TkForall    = "forall"
showToken TkExists    = "exists"
showToken TkSwitch    = "switch"
showToken TkMu        = "mu"
showToken TkInd       = "ind"
showToken TkCon       = "con"
showToken TkDesc      = "Desc"
showToken TkCode      = "Code"
showToken TkDesc1     = "`1"
showToken TkDescS     = "`S"
showToken TkDescX     = "`X"
showToken TkDescInd   = "indDesc"
showToken TkLParen    = "("
showToken TkRParen    = ")"
showToken TkLBracket  = "["
showToken TkRBracket  = "]"
showToken TkLBrace    = "{"
showToken TkRBrace    = "}"
showToken TkTilde     = "~"
showToken TkArrow     = "->"
showToken TkBackSlash = "\\"
showToken TkColon     = ":"
showToken TkSemi      = ";"
showToken TkComma     = ","
showToken TkAst       = "*"
showToken TkEquals    = "="
showToken TkHole      = "_"
showToken TkEOF       = "end-of-file"
showToken (TkError _) = "ERROR!"

-------------------------------------------------------------------------------
-- Lexer state
-------------------------------------------------------------------------------

data LexerState = LS
    { lsContents :: {-# UNPACK #-} !Text
    , lsLocation :: !Loc
    }

instance Monad m => P.Stream LexerState m (Loc, Token) where
    uncons (skipSpace -> ls)
        | T.null (lsContents ls) = return Nothing
        | otherwise              = case scan ls of
            (TkEOF, _) -> return Nothing
            (tok, ls') -> return (Just ((lsLocation ls, tok), ls'))

initLexerState :: FilePath -> ByteString -> LexerState
initLexerState fn bs = LS
    { lsContents = decodeUtf8Lenient bs
    , lsLocation = startLoc fn
    }

decodeUtf8Lenient :: ByteString -> Text
decodeUtf8Lenient = TE.decodeUtf8With TEE.lenientDecode

skipSpace :: LexerState -> LexerState
skipSpace (LS bs loc)
    | Just sfx' <- T.stripPrefix "--" sfx
    , (pfx'', sfx'') <- T.span (/= '\n') sfx'
    = skipSpace $ LS sfx'' (loc `advanceLoc` pfx `advanceLoc` "--" `advanceLoc` pfx'')

    | otherwise
    = LS sfx (loc `advanceLoc` pfx)
  where
    (pfx, sfx) = T.span isSpace bs

-------------------------------------------------------------------------------
-- Char predicates
-------------------------------------------------------------------------------

isSpace :: Char -> Bool
isSpace c = ' ' == c || '\t' == c || '\n' == c

isIdentChar :: Char -> Bool
isIdentChar c
    | isSpace c                = False
    | elem c ('\\':"(){}[]~;") = False
    | otherwise                = isPrint c

-------------------------------------------------------------------------------
-- Scanning function
-------------------------------------------------------------------------------

scan :: LexerState -> (Token, LexerState)
scan ls@(LS contents loc) = case T.uncons contents of
    Nothing                -> (TkEOF,       ls)
    Just ('(' , contents') -> (TkLParen,    LS contents' (advanceLoc loc "("))
    Just (')' , contents') -> (TkRParen,    LS contents' (advanceLoc loc ")"))
    Just ('[' , contents') -> (TkLBracket,  LS contents' (advanceLoc loc "["))
    Just (']' , contents') -> (TkRBracket,  LS contents' (advanceLoc loc "]"))
    Just ('{' , contents') -> (TkLBrace,    LS contents' (advanceLoc loc "{"))
    Just ('}' , contents') -> (TkRBrace,    LS contents' (advanceLoc loc "}"))
    Just ('~' , contents') -> (TkTilde,     LS contents' (advanceLoc loc "~"))
    Just (';' , contents') -> (TkSemi,      LS contents' (advanceLoc loc ";"))
    Just ('\\', contents') -> (TkBackSlash, LS contents' (advanceLoc loc "\\"))
    Just (c,    _        )
        | isIdentChar c -> case T.span isIdentChar contents of
            (pfx, sfx)     -> (classify pfx, LS sfx (advanceLoc loc pfx))

        | otherwise        -> (TkError $ "Unknown character: " ++ show c, ls)

classify :: Text -> Token
classify "define"  = TkDefine
classify "type"    = TkType
classify "eval"    = TkEval
classify "info"    = TkInfo
classify "inline"  = TkInline
classify "macro"   = TkMacro
classify "let"     = TkLet
classify "in"      = TkIn
classify "U"       = TkU
classify "forall"  = TkForall
classify "exists"  = TkExists
classify "switch"  = TkSwitch
classify "Desc"    = TkDesc
classify "`1"      = TkDesc1
classify "`S"      = TkDescS
classify "`X"      = TkDescX
classify "indDesc" = TkDescInd
classify "mu"      = TkMu
classify "con"     = TkCon
classify "ind"     = TkInd
classify "Code"    = TkCode
classify "->"      = TkArrow
classify ":"       = TkColon
classify ","       = TkComma
classify "*"       = TkAst
classify "="       = TkEquals
classify "_"       = TkHole
classify bs        = case T.uncons bs of
    Just ('.', bs') -> TkSelector (mkSelector bs')
    Just (':', bs') -> TkLabel (mkLabel bs')
    _               -> TkIdent (mkName bs)
