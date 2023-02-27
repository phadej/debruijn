{-# LANGUAGE Safe #-}
module DeBruijn.Add (
    Add (AZ, AS),
    addToInt,
    addToSize,
    adding,
    -- * Lemmas
    rzeroAdd,
    unrzeroAdd,
    lzeroAdd,
    unlzeroAdd,
    keepAdd,
    unkeepAdd,
    swapAdd,
    unswapAdd,
) where

import Data.GADT.Show     (GShow (..))
import Data.Kind          (Type)
import Data.Some          (Some (..))
import Data.Type.Equality ((:~:) (..))

import DeBruijn.Ctx
import DeBruijn.Size

-- $setup
-- >>> import DeBruijn

-- | @'Add' n m p@ is an evidence that @n + m = p@.
--
-- Useful when you have an arity @n@ thing and need to extend a context @ctx@ with: @'Add' n ctx ctx'@.
--
-- Using a type representing a graph of a type function is often more convenient than defining type-family to begin with.
--
type Add :: Ctx -> Ctx -> Ctx -> Type
type role Add nominal nominal nominal
data Add n m p where
    AZ :: Add EmptyCtx ctx ctx
    AS :: !(Add n ctx ctx') -> Add (S n) ctx (S ctx')

addToInt :: Add n m p -> Int
addToInt = go 0 where
    go :: Int -> Add n m p -> Int
    go !n AZ     = n
    go !n (AS a) = go (n + 1) a

addToSize :: Add n m p -> Size n
addToSize AZ     = SZ
addToSize (AS a) = SS (addToSize a)

instance Show (Add n m p) where
    showsPrec d a = showsPrec d (addToInt a)

instance GShow (Add n m) where
    gshowsPrec = showsPrec

-- | Add @n@ to some context @ctx@.
--
-- >>> adding (SS (SS SZ))
-- Some 2
--
adding :: Size n -> Some (Add n ctx)
adding SZ     = Some AZ
adding (SS s) = case adding s of Some a -> Some (AS a)

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | @n + 0 ≡ 0@
rzeroAdd :: Size n -> Add n EmptyCtx n
rzeroAdd SZ     = AZ
rzeroAdd (SS s) = AS (rzeroAdd s)

-- | @n + 0 ≡ m → n ≡ m@
unrzeroAdd :: Add n EmptyCtx m -> n :~: m
unrzeroAdd AZ     = Refl
unrzeroAdd (AS a) = case unrzeroAdd a of Refl -> Refl

-- | @0 + n ≡ 0@
lzeroAdd :: Size n -> Add EmptyCtx n n
lzeroAdd _ = AZ

-- | @0 + n ≡ m → n ≡ m@
unlzeroAdd :: Add EmptyCtx n m -> n :~: m
unlzeroAdd AZ = Refl

-- TODO: I'm not happy with the names, but I don't have a good naming scheme for these lemmas.

-- | @n + m ≡ p → n + S m ≡ S p@
keepAdd :: Add n m p -> Add n (S m) (S p)
keepAdd AZ     = AZ
keepAdd (AS a) = AS $ keepAdd a

-- | @n + S m ≡ S p → n + m ≡ p@
unkeepAdd :: Add n (S m) (S p) -> Add n m p
unkeepAdd AZ     = AZ
unkeepAdd (AS a) = swapAdd a

-- | @n + S m ≡ p → S n + m ≡ p@
swapAdd :: Add n (S m) p -> Add (S n) m p
swapAdd AZ     = AS AZ
swapAdd (AS a) = AS $ swapAdd a

-- | @S n + m ≡ p → n + S m ≡ p@
unswapAdd :: Add (S n) m p -> Add n (S m) p
unswapAdd (AS a) = keepAdd a
