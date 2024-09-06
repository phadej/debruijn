module BoundedEvaluation.Pretty (
    Doc,
    ppList,
    ppList1,
    withFresh,
    Pretty (..),
) where

import BoundedEvaluation.Base

import qualified Control.Monad.Trans.State.Strict as S
import qualified Text.PrettyPrint                 as PP

newtype Doc = Doc (S.State Int PP.Doc)

unDoc :: Doc -> S.State Int PP.Doc
unDoc (Doc d) = d

instance Show Doc where
    show (Doc d) = show (S.evalState d 0)

instance IsString Doc where
    fromString s = Doc (return (PP.text s))

ppList :: [Doc] -> Doc
ppList ts = Doc $ do
    ts' <- traverse unDoc ts
    return $ PP.parens $ PP.sep ts'

ppList1 :: Doc -> [Doc] -> Doc
ppList1 h ts = Doc $ do
    h' <- unDoc h
    ts' <- traverse unDoc ts
    return $ PP.parens $ PP.hang h' 2 $ PP.sep ts'

withFresh :: String -> (Doc -> Doc) -> Doc
withFresh s k = Doc $ do
    n <- S.get
    S.put (n + 1)
    unDoc (k (Doc (return (PP.text (s ++ "_" ++ show n)))))

class Pretty term where
    pretty :: Env ctx Doc -> term ctx -> Doc
