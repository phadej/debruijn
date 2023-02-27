module PoriTT.PP (
    Doc,
    A (..),
    -- * Combinators
    ppRender,
    ppAnnotate,
    ppTyArr,
    ppSyArr,
    ppParens,
    ppParensIf,
    pbraceSemi,
    pbraces,
    ppSep,
    ppVCat,
    ppText,
    ppInt,
    ppHanging,
    ppSoftHanging,
    (<+>),
    ($$),
    (<//>),
    (</>),
) where

import Data.Coerce (coerce)
import Data.String (IsString (..))

import qualified Data.Text           as T
import qualified Prettyprinter       as PP
import qualified System.Console.ANSI as ANSI

-- | Annotations
data A
    = AKey
    | ATyp
    | ALbl
    | ACon
    | ASel
    | ACmd
    | AGbl
  deriving (Eq, Ord, Show)

newtype Doc = D (PP.Doc A)

instance IsString Doc where
    fromString s = D (ann s $ fromString s)

ann :: String -> PP.Doc A -> PP.Doc A
ann "U"       = PP.annotate ATyp
ann "forall"  = PP.annotate ATyp
ann "exists"  = PP.annotate ATyp
ann "*"       = PP.annotate ATyp
ann "mu"      = PP.annotate ATyp
ann "Desc"    = PP.annotate ATyp

ann "\\"      = PP.annotate AKey
ann "switch"  = PP.annotate AKey
ann "ind"     = PP.annotate AKey
ann "indDesc" = PP.annotate AKey
ann "="       = PP.annotate AKey
ann ":"       = PP.annotate AKey
ann "{"       = PP.annotate AKey
ann ";"       = PP.annotate AKey
ann "}"       = PP.annotate AKey

ann ","       = PP.annotate ACon
ann "con"     = PP.annotate ACon
ann "`1"      = PP.annotate ACon
ann "`S"      = PP.annotate ACon
ann "`X"      = PP.annotate ACon

ann _         = id

ppTyArr :: Doc
ppTyArr = ppAnnotate ATyp "->"

ppSyArr :: Doc
ppSyArr = ppAnnotate AKey "->"

instance Semigroup Doc where
    D x <> D y = D (x <> y)

instance Show Doc where
    show = ppRender False

ppRender
    :: Bool    -- ^ use colours
    -> Doc
    -> String
ppRender colour (D doc) = renderShowS colour sds ""
  where
    sds = PP.layoutSmart opts doc
    opts = PP.defaultLayoutOptions

renderShowS :: Bool -> PP.SimpleDocStream A -> ShowS
renderShowS _      PP.SFail            = id
renderShowS _      PP.SEmpty           = id
renderShowS colour (PP.SChar c x)      = showChar c . renderShowS colour x
renderShowS colour (PP.SText _l t x)   = showString (T.unpack t) . renderShowS colour x
renderShowS colour (PP.SLine i x)      = showString ('\n' : replicate i ' ') . renderShowS colour x
renderShowS colour (PP.SAnnPush a x)   = renderAnnPush colour a . renderShowS colour x
renderShowS colour (PP.SAnnPop x)      = renderAnnPop colour . renderShowS colour x

renderAnnPush :: Bool -> A -> ShowS
renderAnnPush True  a = showString (ANSI.setSGRCode (sgrCode a))
renderAnnPush False _ = id

renderAnnPop :: Bool -> ShowS
renderAnnPop True  = showString (ANSI.setSGRCode [])
renderAnnPop False = id

ppAnnotate :: A -> Doc -> Doc
ppAnnotate a (D d) = D (PP.annotate a d)

sgrCode :: A -> [ANSI.SGR]
sgrCode ATyp = sgrCode' ANSI.Green
sgrCode AKey = sgrCode' ANSI.Yellow
sgrCode ASel = sgrCode' ANSI.Magenta
sgrCode ALbl = sgrCode' ANSI.Magenta -- keywords and labels with the same color :(
sgrCode AGbl = sgrCode' ANSI.Blue
sgrCode ACon = sgrCode' ANSI.Cyan
sgrCode ACmd = [ANSI.SetConsoleIntensity ANSI.BoldIntensity]

sgrCode' :: ANSI.Color -> [ANSI.SGR]
sgrCode' c = [ANSI.SetColor ANSI.Foreground ANSI.Vivid c]

ppParensIf :: Bool -> Doc -> Doc
ppParensIf True  = ppParens
ppParensIf False = id

ppParens :: Doc -> Doc
ppParens = coerce (PP.parens @A)

pbraceSemi :: [Doc] -> Doc
pbraceSemi = pbraces . coerce (PP.sep @A . PP.punctuate ";")

pbraces :: Doc -> Doc
pbraces d = "{" <> d <> "}"

ppText :: String -> Doc
ppText = coerce (PP.pretty :: String -> PP.Doc A)

ppInt :: Int -> Doc
ppInt = D . PP.pretty

ppHang :: Int -> Doc -> Doc
ppHang i (D d) = D (PP.hang i d)

ppHanging :: Doc -> [Doc] -> Doc
ppHanging d ds = ppHang 2 (ppVCat (d : ds))

ppSoftHanging :: Doc -> [Doc] -> Doc
ppSoftHanging d ds = ppHang 2 (ppSep (d : ds))

ppSep :: [Doc] -> Doc
ppSep = coerce (PP.sep @A)

ppVCat :: [Doc] -> Doc
ppVCat = coerce (PP.vcat @A)

infixr 6 <+>
infixr 5 $$, <//>, </>

(<+>), ($$), (<//>), (</>) :: Doc -> Doc -> Doc

(<+>) = coerce ((PP.<+>) @A)
x $$ y = ppVCat [x, y]

x <//> y = ppSoftHanging x [y]

x </> y = ppSep [x, y]
