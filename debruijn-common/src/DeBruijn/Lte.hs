module DeBruijn.Lte (
    Lte (..),
) where

import Data.Kind (Type)

import DeBruijn.Ctx

-- | @'Lte' ctx ctx'@ is evidence that @ctx'@ is smaller than of @'ctx'@, /less-than-or-equal/,
-- and produced by simple skipping only, i.e. nothing is inserted into @ctx@, only appended
-- to the end.
--
type Lte :: Ctx -> Ctx -> Type
type role Lte nominal nominal
data Lte ctx ctx' where
    LZ :: Lte ctx ctx
    LS :: !(Lte ctx ctx') -> Lte ctx (S ctx')
