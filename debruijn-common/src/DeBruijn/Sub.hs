module DeBruijn.Sub (
    -- * Substitution
    Sub (..),
    unSub,
    substIdx,
    emptySub,
    snocSub,
    keepSub,
    weakenSub,
    nameMe,
    -- ** Category
    idSub,
    compSub,
    -- * Classes
    Var (..),
    Subst (..),
) where

import Data.Coerce (coerce)
import Data.Kind   (Constraint, Type)
import Data.Proxy  (Proxy (..))

import DeBruijn.Ctx
import DeBruijn.Env
import DeBruijn.Idx
import DeBruijn.Ren
import DeBruijn.Size
import DeBruijn.Wk

-- | Substitutions.
type Sub :: (Ctx -> Type) -> Ctx -> Ctx -> Type
newtype Sub t ctx ctx' = MkSub (Env ctx (t ctx'))

unSub :: Sub t ctx ctx' -> Env ctx (t ctx')
unSub = coerce

-- | Substitute index.
substIdx :: Sub t ctx ctx' -> Idx ctx -> t ctx'
substIdx (MkSub ts) i = lookupEnv i ts

-- | Substitution from empty context.
emptySub :: Sub t EmptyCtx ctx'
emptySub = MkSub EmptyEnv

snocSub :: Sub t ctx ctx' -> t ctx' -> Sub t (S ctx) ctx'
snocSub (MkSub s) t = MkSub (s :> t)

keepSub :: (Renamable t, Var t) => Sub t ctx ctx' -> Sub t (S ctx) (S ctx')
keepSub (MkSub ts) = MkSub (fmap (weaken wk1) ts :> var IZ)

-- | Precompose 'Sub' with weakening.
weakenSub :: Wk ctx ctx' -> Sub t ctx' ctx'' -> Sub t ctx ctx''
weakenSub w (MkSub ts) = MkSub (weakenEnv w ts)

-- TODO:
nameMe :: Renamable t => Sub t ctx ctx' -> Wk ctx' ctx'' -> Sub t ctx ctx''
nameMe (MkSub ts) w = MkSub (fmap (weaken w) ts)

-------------------------------------------------------------------------------
-- Classes
-------------------------------------------------------------------------------

-- | Terms which contain indices as variables.
type Var :: (Ctx -> Type) -> Constraint
class Var t where
    var :: Idx ctx -> t ctx

-- | Terms which we can subsitute into.
type Subst :: (Ctx -> Type) -> Constraint
class Var t => Subst t where
    subst :: Sub t ctx ctx' -> t ctx -> t ctx'

instance Var Proxy where
    var _ = Proxy

instance Subst Proxy where
    subst _ _ = Proxy

instance Var Idx where
    var = id

instance Subst Idx where
    subst = substIdx

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

-- | Identity substitution
idSub :: Var t => Size ctx -> Sub t ctx ctx
idSub s = MkSub $ tabulateEnv s var

-- | Substitution composition.
compSub :: Subst t => Sub t ctx ctx' -> Sub t ctx' ctx'' -> Sub t ctx ctx''
compSub (MkSub s) s' = MkSub (fmap (subst s') s)
