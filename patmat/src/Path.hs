{-# LANGUAGE PolyKinds #-}
module Path (
    Path (..),
    append,
) where

import Data.Kind (Type)

-- | Transitive-reflexive closure.
type Path :: (k -> k -> Type) -> k -> k -> Type
data Path p a b where
    End  :: Path p a a
    Cons :: p a b -> Path p b c -> Path p a c

append :: Path p xs ys -> Path p ys zs -> Path p xs zs
append End         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
