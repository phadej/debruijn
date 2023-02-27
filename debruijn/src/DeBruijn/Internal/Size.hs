{-# LANGUAGE Unsafe #-}
module DeBruijn.Internal.Size (
    Size (SZ, SS, UnsafeSize),
    unSS,
    sizeToInt,
    pattern S1,
    pattern S2,
    pattern S3,
    pattern S4,
    pattern S5,
    pattern S6,
    pattern S7,
    pattern S8,
    pattern S9,
) where

import Data.EqP           (EqP (..))
import Data.GADT.Compare  (GCompare (..), GEq (..), GOrdering (..))
import Data.GADT.Show     (GShow (..))
import Data.Kind          (Type)
import Data.OrdP          (OrdP (..))
import Data.Type.Equality (TestEquality (testEquality), (:~:) (Refl))
import Unsafe.Coerce      (unsafeCoerce)

import DeBruijn.Ctx

-- | Term level witness of the size of a context.
--
-- >>> SZ
-- 0
--
-- >>> SS (SS SZ)
-- 2
--
type Size :: Ctx -> Type
type role Size nominal

newtype Size ctx = UnsafeSize { _sizeToInt :: Int }

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

-- | Unapply 'SS'. Occasionally more useful than pattern matching.
unSS :: Size (S ctx) -> Size ctx
unSS (SS x) = x

-- | Convert 'Size' to 'Int.
sizeToInt :: Size ctx -> Int
sizeToInt = _sizeToInt

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (Size ctx) where
    showsPrec d (UnsafeSize i) = showsPrec d i

instance GShow Size where
    gshowsPrec = showsPrec

instance Eq (Size ctx) where
    _ == _ = True

instance Ord (Size ctx) where
    compare _ _ = EQ

instance EqP Size where
    eqp (UnsafeSize n) (UnsafeSize m) = n == m

instance OrdP Size where
    comparep (UnsafeSize n) (UnsafeSize m) = compare n m

instance GEq Size where
    geq (UnsafeSize n) (UnsafeSize m) =
        if n == m then Just (unsafeCoerce Refl) else Nothing

instance GCompare Size where
    gcompare (UnsafeSize n) (UnsafeSize m) = case compare n m of
        LT -> GLT
        EQ -> unsafeCoerce GEQ
        GT -> GGT

instance TestEquality Size where
    testEquality = geq

-------------------------------------------------------------------------------
-- Pattern synonyms
-------------------------------------------------------------------------------

-- We need a GADT to implement pattern synonyms.
type ViewSize :: Ctx -> Type
type role ViewSize nominal
data ViewSize ctx where
    SZ' :: ViewSize EmptyCtx
    SS' :: Size n -> ViewSize (S n)

viewSize :: Size n -> ViewSize n
viewSize (UnsafeSize 0) = unsafeCoerce SZ'
viewSize (UnsafeSize n) = unsafeCoerce (SS' (UnsafeSize (n - 1)))

pattern SZ :: () => (m ~ EmptyCtx) => Size m
pattern SZ <- (viewSize -> SZ')
  where SZ = UnsafeSize 0

pattern SS :: () => (m ~ S n) => Size n -> Size m
pattern SS n <- (viewSize -> SS' n)
  where SS n = UnsafeSize (_sizeToInt n + 1)

{-# COMPLETE SZ, SS #-}

-------------------------------------------------------------------------------
-- Sizes
-------------------------------------------------------------------------------

pattern S1 :: () => (m ~ Ctx1) => Size m
pattern S1 = SS SZ

pattern S2 :: () => (m ~ Ctx2) => Size m
pattern S2 = SS S1

pattern S3 :: () => (m ~ Ctx3) => Size m
pattern S3 = SS S2

pattern S4 :: () => (m ~ Ctx4) => Size m
pattern S4 = SS S3

pattern S5 :: () => (m ~ Ctx5) => Size m
pattern S5 = SS S4

pattern S6 :: () => (m ~ Ctx6) => Size m
pattern S6 = SS S5

pattern S7 :: () => (m ~ Ctx7) => Size m
pattern S7 = SS S6

pattern S8 :: () => (m ~ Ctx8) => Size m
pattern S8 = SS S7

pattern S9 :: () => (m ~ Ctx9) => Size m
pattern S9 = SS S8
