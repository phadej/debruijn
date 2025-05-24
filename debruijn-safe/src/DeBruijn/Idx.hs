{-# LANGUAGE Safe #-}
-- | de Bruijn indices for well-scoped terms.
module DeBruijn.Idx (
    -- * de Bruijn indices
    Idx (IZ,IS),
    absurdIdx,
    unIdx,
    idxToInt,
    -- * Common indices
    pattern I1,
    pattern I2,
    pattern I3,
    pattern I4,
    pattern I5,
    pattern I6,
    pattern I7,
    pattern I8,
    pattern I9,
) where

import Data.Kind    (Type)
import DeBruijn.Ctx

-------------------------------------------------------------------------------
-- de Bruijn indices
-------------------------------------------------------------------------------

-- | de Bruijn indices.
--
-- >>> IS (IS (IS IZ))
-- 3
--
type Idx :: Ctx -> Type
type role Idx nominal

data Idx ctx where
    IZ :: Idx (S ctx)
    IS :: !(Idx ctx) -> Idx (S ctx)

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

-- | Convert index to 'Int'.
idxToInt :: Idx ctx -> Int
idxToInt = go 0 where
    go :: Int -> Idx j -> Int
    go !acc IZ = acc
    go acc (IS n) = go (acc + 1) n

-- | Derive anything from index into empty scope.
--
-- Note: don't use @EmptyCase@ as it doesn't work for unsafe representation.
absurdIdx :: Idx EmptyCtx -> a
absurdIdx x = x `seq` error "absurd: Idx Z"

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq (Idx ctx)
deriving instance Ord (Idx ctx)

instance Show (Idx j) where
    showsPrec d = showsPrec d . idxToInt

-------------------------------------------------------------------------------
-- Common Combinators
-------------------------------------------------------------------------------

-- | Case on 'Idx'. (compare to 'maybe').
unIdx :: a -> (Idx n -> a) -> Idx (S n) -> a
unIdx z _ IZ     = z
unIdx _ s (IS x) = s x

pattern I1 :: () => (m ~ S (S n)) => Idx m
pattern I1 = IS IZ

pattern I2 :: () => (m ~ S (S (S n))) => Idx m
pattern I2 = IS I1

pattern I3 :: () => (m ~ S (S (S (S n)))) => Idx m
pattern I3 = IS I2

pattern I4 :: () => (m ~ S (S (S (S (S n))))) => Idx m
pattern I4 = IS I3

pattern I5 :: () => (m ~ S (S (S (S (S (S n)))))) => Idx m
pattern I5 = IS I4

pattern I6 :: () => (m ~ S (S (S (S (S (S (S n))))))) => Idx m
pattern I6 = IS I5

pattern I7 :: () => (m ~ S (S (S (S (S (S (S (S n)))))))) => Idx m
pattern I7 = IS I6

pattern I8 :: () => (m ~ S (S (S (S (S (S (S (S (S n))))))))) => Idx m
pattern I8 = IS I7

pattern I9 :: () => (m ~ S (S (S (S (S (S (S (S (S (S n)))))))))) => Idx m
pattern I9 = IS I8
