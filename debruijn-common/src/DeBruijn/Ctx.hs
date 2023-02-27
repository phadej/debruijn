{-# LANGUAGE Safe #-}
module DeBruijn.Ctx (
    Ctx,
    EmptyCtx,
    S,
    Ctx1, Ctx2, Ctx3, Ctx4, Ctx5, Ctx6, Ctx7, Ctx8, Ctx9,
) where

import Data.Kind (Type)
import Data.Nat  (Nat (..))

-- | Context counts variables, in other words context is just a natural number.
type Ctx :: Type
type Ctx = Nat

-- | Empty context is zero.
type EmptyCtx :: Ctx
type EmptyCtx = Z

-- | And context extension is a successor.
type S :: Ctx -> Ctx
type S = 'S

type Ctx1 = S EmptyCtx
type Ctx2 = S Ctx1
type Ctx3 = S Ctx2
type Ctx4 = S Ctx3
type Ctx5 = S Ctx4
type Ctx6 = S Ctx5
type Ctx7 = S Ctx6
type Ctx8 = S Ctx7
type Ctx9 = S Ctx8
