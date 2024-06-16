module Constructor (
    Constructor (..),
) where

import Control.Monad     (guard)
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import Data.Kind         (Type)

import DeBruijn

type Constructor :: Ctx -> Type
data Constructor arity where
    Constructor :: String -> !(Size arity) -> Constructor arity

deriving instance Show (Constructor arity)

instance GEq Constructor where
    geq (Constructor n1 s1) (Constructor n2 s2) = do
        guard (n1 == n2)
        geq s1 s2

instance GCompare Constructor where
    gcompare (Constructor n1 s1) (Constructor n2 s2) = case compare n1 n2 of
        GT -> GGT
        LT -> GLT
        EQ -> gcompare s1 s2
