{-# LANGUAGE PolyKinds #-}
module PatMat where

import Data.Kind (Type)

import DeBruijn

type Expr :: ctx -> Type
data Expr ctx where
    Lam :: Expr (S ctx) -> Expr ctx

type Pat :: Ctx -> Ctx -> Type
data Pat n m where
    VarP :: Pat ctx (S ctx)

type Clause :: Ctx -> Type
data Clause ctx where
    Clause :: Pat ctx ctx' -> Expr ctx' -> Clause ctx

-- | Transitive-reflexive closure.
type Path :: (k -> k -> Type) -> k -> k -> Type
data Path p a b where
    End :: Path p a a
    Cons :: p a b -> Path p b c -> Path p a c

elab :: [Clause ctx] -> Expr ctx
elab = undefined
