module PoriTT.Loc (
    Loc (..),
    startLoc,
    advanceLoc,
    prettyLoc,
) where

import qualified Data.Text as T

import PoriTT.Base
import PoriTT.PP

-- | Source location
data Loc = Loc
    { locFile   :: !FilePath
    , locLine   :: !Int
    , locColumn :: !Int
    }
  deriving (Eq)

instance Show Loc where
    showsPrec _ _ = showString "Loc"

-- | Starting location in a file.
startLoc :: FilePath -> Loc
startLoc fn = Loc fn 1 1

advanceLoc :: Loc -> Text -> Loc
advanceLoc loc bs = T.foldl' advanceChar loc bs

advanceChar :: Loc -> Char -> Loc
advanceChar (Loc fn l _) '\n' = Loc fn (l + 1) 1
advanceChar (Loc fn l c) _    = Loc fn l       (c + 1)

prettyLoc :: Loc -> Doc
prettyLoc (Loc fn l c) = ppText (fn ++ ":" ++ show l ++ ":" ++ show c)
