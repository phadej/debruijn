{-# LANGUAGE PolyKinds #-}
module PatMat where

import Data.Kind (Type)

import DeBruijn

singleton :: a -> [a]
singleton x = [x]

type ConName = String

type Expr :: ctx -> Type
data Expr ctx where
    Lam :: Expr (S ctx) -> Expr ctx

type Pat :: Ctx -> Ctx -> Type
data Pat n m where
    VarP :: Pat ctx (S ctx)
    ConP :: ConName -> Path Pat ctx ctx' -> Pat ctx ctx' 

type Clause :: Ctx -> Type
data Clause ctx where
    Clause :: Pat ctx ctx' -> Expr ctx' -> Clause ctx

-- | Transitive-reflexive closure.
type Path :: (k -> k -> Type) -> k -> k -> Type
data Path p a b where
    End :: Path p a a
    Cons :: p a b -> Path p b c -> Path p a c

type ClauseN :: Ctx -> Type
data ClauseN ctx where
    ClauseN :: Path Pat ctx ctx' -> Expr ctx' -> ClauseN ctx

elab :: [ClauseN ctx] -> Expr ctx
elab [] = error "no clauses"
elab (ClauseN End                       e : _)  = e -- TODO: warning, unreachable clauses
elab (ClauseN (Cons VarP ps)            e : _)  = Lam $ elab $ singleton $ ClauseN ps e
elab (ClauseN (Cons (ConP con cps) ps') e : cs) = _
