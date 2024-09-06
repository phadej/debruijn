module BoundedEvaluation.Haskell (
    two,
    ind,
    add,
    mult,
    ex1,
    ex2,
) where

import Data.Function (fix)
import Data.Nat      (Nat (..))

two :: Nat
two = S (S Z)

ind :: a -> (a -> a) -> Nat -> a
ind = \z s -> fix $ \recur n -> case n of
    Z    -> z
    S n' -> s (recur n')

add :: Nat -> Nat -> Nat
add = \n m -> ind m (\n' -> S n') n

mult :: Nat -> Nat -> Nat
mult = \n m -> ind Z (add m) n

-- | Addition example
--
-- @2 + 2 + 2@
--
-- >>> ex1
-- 6
ex1 :: Nat
ex1 = add two (add two two)

-- | Multiplication example
--
-- @2 * 3@
--
-- >>> ex2
-- 6
ex2 :: Nat
ex2 = mult two (S two)
