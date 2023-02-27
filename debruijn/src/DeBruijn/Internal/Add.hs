{-# LANGUAGE Unsafe #-}
module DeBruijn.Internal.Add (
    Add (AZ, AS, UnsafeAdd),
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


import Data.Coerce        (coerce)
import Data.GADT.Show     (GShow (..))
import Data.Kind          (Type)
import Data.Some          (Some (..))
import Data.Type.Equality ((:~:) (Refl))
import Unsafe.Coerce      (unsafeCoerce)

import DeBruijn.Ctx
import DeBruijn.Internal.Size

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

newtype Add n m p = UnsafeAdd { _addToInt :: Int }

addToInt :: Add n m p -> Int
addToInt = _addToInt

addToSize :: Add n m p -> Size n
addToSize (UnsafeAdd n) = UnsafeSize n

instance Show (Add n m p) where
    showsPrec d a = showsPrec d (addToInt a)

instance GShow (Add n m) where
    gshowsPrec = showsPrec

type ViewAdd :: Ctx -> Ctx -> Ctx -> Type
type role ViewAdd nominal nominal nominal
data ViewAdd n m p where
    AZ' :: ViewAdd EmptyCtx ctx ctx
    AS' :: !(Add n ctx ctx') -> ViewAdd (S n) ctx (S ctx')

viewAdd :: Add n m p -> ViewAdd n m p
viewAdd (UnsafeAdd n)
    | n <= 0    = unsafeCoerce AZ'
    | otherwise = unsafeCoerce (AS' (UnsafeAdd (n - 1)))

pattern AZ :: () => (n ~ EmptyCtx, m ~ p) => Add n m p
pattern AZ <- (viewAdd -> AZ')
  where AZ = UnsafeAdd 0

pattern AS :: () => (n ~ S n', p ~ S p') => Add n' m p' -> Add n m p
pattern AS a <- (viewAdd -> AS' a)
  where AS a = UnsafeAdd (_addToInt a + 1)

{-# COMPLETE AZ, AS #-}

-- | Add @n@ to some context @ctx@.
--
-- >>> adding (SS (SS SZ))
-- Some 2
--
adding :: Size n -> Some (Add n ctx)
adding (UnsafeSize n) = Some (UnsafeAdd n)

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | @n + 0 ≡ 0@
rzeroAdd :: Size n -> Add n EmptyCtx n
rzeroAdd (UnsafeSize n) = UnsafeAdd n

-- | @n + 0 ≡ m → n ≡ m@
unrzeroAdd :: Add n EmptyCtx m -> n :~: m
unrzeroAdd (UnsafeAdd !_) = unsafeCoerce Refl

-- | @0 + n ≡ 0@
lzeroAdd :: Size n -> Add EmptyCtx n n
lzeroAdd _ = AZ

-- | @0 + n ≡ m → n ≡ m@
unlzeroAdd :: Add EmptyCtx n m -> n :~: m
unlzeroAdd AZ = Refl

-- | @n + m ≡ p → n + S m ≡ S p@
keepAdd :: Add n m p -> Add n (S m) (S p)
keepAdd = coerce

-- | @n + S m ≡ S p → n + m ≡ p@
unkeepAdd :: Add n (S m) (S p) -> Add n m p
unkeepAdd = coerce

-- | @n + S m ≡ p → S n + m ≡ p@
swapAdd :: Add n (S m) p -> Add (S n) m p
swapAdd (UnsafeAdd n) = UnsafeAdd (n + 1)

-- | @S n + m ≡ p → n + S m ≡ p@
unswapAdd :: Add (S n) m p -> Add n (S m) p
unswapAdd (UnsafeAdd n) = UnsafeAdd (n - 1)
