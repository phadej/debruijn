{-# LANGUAGE Safe #-}
module DeBruijn.Size (
    Size (SZ, SS),
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
import Data.GADT.Compare  (GCompare (..), GEq (..), GOrdering (..), defaultCompare, defaultEq)
import Data.GADT.Show     (GShow (..))
import Data.Kind          (Type)
import Data.OrdP          (OrdP (..))
import Data.Type.Equality (TestEquality (testEquality), (:~:) (Refl))

import DeBruijn.Ctx

-- | Term level witness of the size of the context.
--
-- >>> SZ
-- 0
--
-- >>> SS (SS SZ)
-- 2
--
type Size :: Ctx -> Type
data Size ctx where
    SZ :: Size EmptyCtx
    SS :: !(Size ctx) -> Size (S ctx)

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

unSS :: Size (S ctx) -> Size ctx
unSS (SS x) = x

sizeToInt :: Size ctx -> Int
sizeToInt = go 0 where
    go :: Int -> Size ctx -> Int
    go !n SZ     = n
    go  n (SS s) = go (n + 1) s

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (Size ctx) where
    showsPrec d s = showsPrec d (sizeToInt s)

instance GShow Size where
    gshowsPrec = showsPrec

instance Eq (Size ctx) where
    _ == _ = True

instance Ord (Size ctx) where
    compare _ _ = EQ
    _ <= _ = True
    _ >= _ = True
    _ < _ = False
    _ > _ = False
    min x _ = x
    max x _ = x

instance EqP Size where
    eqp = defaultEq

instance OrdP Size where
    comparep = defaultCompare

instance GEq Size where
    geq SZ     SZ     = Just Refl
    geq (SS n) (SS m) = do
        Refl <- geq n m
        Just Refl
    geq _      _      = Nothing

instance GCompare Size where
    gcompare SZ     SZ     = GEQ
    gcompare SZ     (SS _) = GLT
    gcompare (SS _) SZ     = GGT
    gcompare (SS n) (SS m) = case gcompare n m of
        GLT -> GLT
        GEQ -> GEQ
        GGT -> GGT

instance TestEquality Size where
    testEquality = geq

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
