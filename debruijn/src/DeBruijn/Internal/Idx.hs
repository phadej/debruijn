{-# LANGUAGE Unsafe #-}
-- | de Bruijn indices for well-scoped terms.
module DeBruijn.Internal.Idx (
    -- * de Bruijn indices
    Idx (IZ, IS, UnsafeIdx),
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

import Unsafe.Coerce (unsafeCoerce)

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

newtype Idx j = UnsafeIdx { _idxToInt :: Int }

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

-- | Convert index to 'Int'.
idxToInt :: Idx ctx -> Int
idxToInt = _idxToInt

-- | Derive anything from index into empty scope.
--
-- Note: don't use @EmptyCase@ on 'Idx' as it doesn't work for unsafe representation.
--
absurdIdx :: Idx EmptyCtx -> a
absurdIdx x = x `seq` error "absurd: Idx Z"

-------------------------------------------------------------------------------
-- Pattern synonyms
-------------------------------------------------------------------------------

-- We need a GADT to implement pattern synonyms.
type ViewIdx :: Ctx -> Type
type role ViewIdx nominal
data ViewIdx n where
    IZ' :: ViewIdx (S n)
    IS' :: Idx n -> ViewIdx (S n)

viewIdx :: Idx n -> ViewIdx n
viewIdx (UnsafeIdx 0) = unsafeCoerce IZ'
viewIdx (UnsafeIdx n) = unsafeCoerce (IS' (UnsafeIdx (n - 1)))

pattern IZ :: () => (m ~ S n) => Idx m
pattern IZ <- (viewIdx -> IZ')
  where IZ = UnsafeIdx 0

pattern IS :: () => (m ~ S n) => Idx n -> Idx m
pattern IS n <- (viewIdx -> IS' n)
  where IS n = UnsafeIdx (idxToInt n + 1)

{-# COMPLETE IZ, IS #-}

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq (Idx n)
deriving instance Ord (Idx n)

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
