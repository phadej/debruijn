module Binder (
    -- * Binders can be nudged
    Binder (..),
    Nudged (..),
    -- * Single variable binder
    Bind (..),
) where

import Data.Kind (Type)

import DeBruijn
import Path
import Name

-------------------------------------------------------------------------------
-- Binders
-------------------------------------------------------------------------------

class Binder bind where
    nudge :: Wk n m -> bind n p -> Nudged bind p m

type Nudged :: (Ctx -> Ctx -> Type) -> Ctx -> Ctx -> Type
data Nudged bind p m where
    Nudged :: Wk p q -> bind m q -> Nudged bind p m

instance Binder bind => Binder (Path bind) where
    nudge wk End = Nudged wk End
    nudge wk (Cons b bs) = case nudge wk b of
        Nudged wk' b' -> case nudge wk' bs of
            Nudged wk'' bs' -> Nudged wk'' (Cons b' bs')

-------------------------------------------------------------------------------
-- Bind: simple binder
-------------------------------------------------------------------------------

data Bind ctx ctx' where
    Bind :: !Name -> Bind ctx (S ctx)

instance Binder Bind where
    nudge wk (Bind n) = Nudged (KeepWk wk) (Bind n)
