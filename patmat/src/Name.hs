module Name (
    Name (..),
) where

import Data.String (IsString (..))

-- | (Irrelevant) names
newtype Name = Name String
    deriving newtype (Show, IsString)

instance Eq Name where
    _ == _ = True

