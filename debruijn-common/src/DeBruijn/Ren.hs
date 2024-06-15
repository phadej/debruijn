{-# LANGUAGE Safe #-}
module DeBruijn.Ren (
    -- * Renamings
    Ren (..),
    renameIdx,
    keepRen,
    skipRen,
    absurdRen,
    wkToRen,
    -- ** Category
    idRen,
    compRen,
    -- * Applicative renamings
    RenA (..),
    renameIdxA,
    keepRenA,
    unusedIdx,
    -- * Renameble things
    IdxMapping (..),
    keepAdd,
    Weaken (..),
    Rename (..),
    RenameA (..),
    defaultRename,
    defaultWeaken,
) where

import Data.Functor.Identity (Identity (..))
import Data.Kind             (Constraint, Type)
import Data.Proxy            (Proxy (..))

import DeBruijn.Add
import DeBruijn.Ctx
import DeBruijn.Env
import DeBruijn.Idx
import DeBruijn.Size
import DeBruijn.Wk

import TrustworthyCompat (coerce)

-------------------------------------------------------------------------------
-- Renamings
-------------------------------------------------------------------------------

-- | Renamings are mappings of de Bruijn indices.
--
-- One possible representation is just @Idx ctx -> Idx ctx'@,
-- but using 'Env' makes this representation inspectable
-- and (hopefully) makes 'renameIdx' perform better.
--
-- On the other hand, 'idRen' requires @'Size' ctx@.
-- However this isn't an issue, as either there is 'Size' or using 'Wk' is an option.
type Ren :: Ctx -> Ctx -> Type
newtype Ren ctx ctx' = MkRen (Env ctx (Idx ctx'))

-- | Rename de Bruijn index.
renameIdx :: Ren ctx ctx' -> Idx ctx -> Idx ctx'
renameIdx (MkRen js) i = lookupEnv i js

-- | Identity renaming.
idRen :: Size ctx -> Ren ctx ctx
idRen s = MkRen $ tabulateEnv s id

-- | Lift renaming (used when going under a binder).
keepRen :: Ren ctx ctx' -> Ren (S ctx) (S ctx')
keepRen (MkRen js) = MkRen (fmap IS js :> IZ)

skipRen :: Ren ctx ctx' -> Ren ctx (S ctx')
skipRen (MkRen js) = MkRen (fmap IS js)

-- | Convert 'Wk' to 'Ren'.
--
-- Note post and precompositions won't need 'Size'.
wkToRen :: Size ctx -> Wk ctx ctx' -> Ren ctx ctx'
wkToRen s      IdWk       = idRen s
wkToRen s      (SkipWk w) = skipRen (wkToRen s w)
wkToRen (SS s) (KeepWk w) = keepRen (wkToRen s w)

-- | Renaming composition.
compRen :: Ren ctx ctx' -> Ren ctx' ctx'' -> Ren ctx ctx''
compRen (MkRen r) r' = MkRen (fmap (rename r') r)

-- | It's simple to have no indices in any context.
absurdRen :: Ren EmptyCtx ctx
absurdRen = MkRen EmptyEnv

-------------------------------------------------------------------------------
-- Applicative renamings
-------------------------------------------------------------------------------

type RenA :: (Type -> Type) -> Ctx -> Ctx -> Type
newtype RenA f ctx ctx' = MkRenA (Env ctx (f (Idx ctx')))

-- | Lift renaming (used when going under a binder).
keepRenA :: Applicative f => RenA f ctx ctx' -> RenA f (S ctx) (S ctx')
keepRenA (MkRenA js) = MkRenA (fmap (fmap IS) js :> pure IZ)

unusedIdx :: Size ctx -> RenA Maybe (S ctx) ctx
unusedIdx s = MkRenA $ tabulateEnv (SS s) $ unIdx Nothing Just

-------------------------------------------------------------------------------
-- Renameble & RenamebleA
-------------------------------------------------------------------------------

-- | 'IdxMapping' generalizes over various index mappings, also effectful ones.
type IdxMapping :: (Type -> Type) -> (Ctx -> Ctx -> Type) -> Constraint
class Applicative f => IdxMapping f t | t -> f where
    -- | 'IdxMapping' action.
    mapIdx :: t ctx ctx' -> Idx ctx -> f (Idx ctx')

    -- | 'keep' is often called @lift@, but we stick with 'Wk' terminology.
    -- One benefit is that the name 'keep' is less likely to clash.
    keep   :: t ctx ctx' -> t (S ctx) (S ctx')

    -- | Compose weakening with an index mapping.
    --
    -- This is useful when you have explicit weakening in your terms.
    -- (a similar idea as in @bound@'s @Scope@ possibly lifting whole term).
    weakenIdxMapping :: Wk ctx ctx' -> t ctx' ctx'' -> t ctx ctx''

-- | 'keep' 'IdxMapping' @arity@ times.
keepAdd
    :: IdxMapping f m
    => Add arity ctxA ctxA'
    -> m ctxA ctxB
    -> (forall ctxB'. Add arity ctxB ctxB' -> m ctxA' ctxB' -> r)
    -> r
keepAdd AZ     w kont = kont AZ w
keepAdd (AS a) w kont = keepAdd a w $ \a' w' -> kont (AS a') (keep w')

instance IdxMapping Identity Wk where
    keep = KeepWk
    mapIdx w x = Identity (weakenIdx w x)
    weakenIdxMapping = compWk

instance IdxMapping Identity Ren where
    keep = keepRen
    mapIdx w x = Identity (renameIdx w x)
    weakenIdxMapping w (MkRen is) = MkRen (weakenEnv w is)

instance Applicative f => IdxMapping f (RenA f) where
    keep = keepRenA
    mapIdx = renameIdxA
    weakenIdxMapping w (MkRenA is) = MkRenA (weakenEnv w is)

renameIdxA :: RenA f ctx ctx' -> Idx ctx -> f (Idx ctx')
renameIdxA (MkRenA js) i = lookupEnv i js

-- | Renameble things.
--
-- For most terms it's enough to define a single traversal: an instance of 'RenamebleA' type-class,
-- and then define 'Renameble' as:
--
-- @
-- instance 'Renameble' Term where 'rename' = 'defaultRename'; 'weaken' = 'defaultWeaken'
-- @
--
class Weaken t where
    weaken :: Wk n m -> t n -> t m

class Weaken t => Rename t where
    rename :: Ren n m -> t n -> t m

-- | 'rename' implementation using 'grename'.
defaultRename :: forall t n m. RenameA t => Ren n m -> t n -> t m
defaultRename = coerce (grename @t @Ren @Identity @n @m)

-- | 'weaken' implementation using 'grename'.
defaultWeaken :: forall t n m. RenameA t => Wk n m -> t n -> t m
defaultWeaken = coerce (grename @t @Wk @Identity @n @m)

-- | Effectful renamings.
--
-- An common example is checking whether a binding is used:
--
-- @
-- Just t' <- 'renameA' 'unusedIdx' t
-- @
--
class Rename t => RenameA t where
    renameA :: forall f ctx ctx'. Applicative f => RenA f ctx ctx' -> t ctx -> f (t ctx')
    renameA = grename

    -- | Generic renaming of a term @t@ using any 'IdxMapping'.
    grename :: forall m f ctx ctx'. IdxMapping f m => m ctx ctx' -> t ctx -> f (t ctx')

instance Weaken Proxy where
     weaken _ _ = Proxy

instance Rename Proxy where
    rename _ _ = Proxy

instance RenameA Proxy where
    grename _ _ = pure Proxy

instance Weaken Idx where
    weaken = weakenIdx

instance Rename Idx where
    rename = renameIdx

instance RenameA Idx where
    grename = mapIdx

instance Weaken (Ren n) where
    weaken w (MkRen js) = MkRen (fmap (weaken w) js)

instance Rename (Ren n) where
    rename r r' = compRen r' r
