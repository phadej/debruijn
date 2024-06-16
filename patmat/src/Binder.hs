module Binder (
    -- * Binders can be nudged
    Binder (..),
    Nudged (..),
    -- * Single variable binder
    Bind (..),
) where

import Data.Kind (Type)
import Data.Functor.Identity (Identity (..))

import DeBruijn
import Path
import Name

-------------------------------------------------------------------------------
-- Binders
-------------------------------------------------------------------------------

class Binder bind where
    nudge :: IdxMapping Identity t => t n m -> bind n p -> Nudged t bind p m

type Nudged :: (Ctx -> Ctx -> Type) -> (Ctx -> Ctx -> Type) -> Ctx -> Ctx -> Type
data Nudged t bind p m where
    Nudged :: t p q -> bind m q -> Nudged t bind p m

instance Binder bind => Binder (Path bind) where
    nudge wk End = Nudged wk End
    nudge wk (Cons b bs) = case nudge wk b of
        Nudged wk' b' -> case nudge wk' bs of
            Nudged wk'' bs' -> Nudged wk'' (Cons b' bs')

instance Binder bind => Binder (PathN bind arity) where
    nudge wk EndN = Nudged wk EndN
    nudge wk (ConsN b bs) = case nudge wk b of
        Nudged wk' b' -> case nudge wk' bs of
            Nudged wk'' bs' -> Nudged wk'' (ConsN b' bs')

-------------------------------------------------------------------------------
-- Bind: simple binder
-------------------------------------------------------------------------------

data Bind ctx ctx' where
    Bind :: !Name -> Bind ctx (S ctx)

instance Binder Bind where
    nudge wk (Bind n) = Nudged (keep wk) (Bind n)

deriving instance Show (Bind ctx ctx')
