{-# LANGUAGE PolyKinds #-}
module Path (
    Path (..),
    append,
    PathN (..),
) where

import Data.Kind (Type)
import Data.Nat  (Nat (S, Z))

-- | Transitive-reflexive closure.
type Path :: (k -> k -> Type) -> k -> k -> Type
data Path p a b where
    End  :: Path p a a
    Cons :: p a b -> Path p b c -> Path p a c

append :: Path p xs ys -> Path p ys zs -> Path p xs zs
append End         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

deriving instance (forall x y. Show (p x y)) => Show (Path p xs ys)

type PathN :: (k -> k -> Type) -> Nat -> k -> k -> Type
data PathN p n a b where
    EndN :: PathN p Z a a
    ConsN :: p a b -> PathN p n b c -> PathN p (S n) a c

deriving instance (forall x y. Show (p x y)) => Show (PathN p n xs ys)
