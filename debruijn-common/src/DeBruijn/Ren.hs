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
    -- * Contractions
    unusedIdx,
    -- * Renameble things
    Keep (..),
    keepAdd,
    Weaken (..),
    Contract (..),
    Rename (..),
) where

import Data.Kind  (Constraint, Type)
import Data.Proxy (Proxy (..))

import DeBruijn.Add
import DeBruijn.Ctx
import DeBruijn.Env
import DeBruijn.Idx
import DeBruijn.Size
import DeBruijn.Wk

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

unusedIdx :: Wk ctx (S ctx)
unusedIdx = wk1

-------------------------------------------------------------------------------
-- Renameble & RenamebleA
-------------------------------------------------------------------------------

type Keep :: (Ctx -> Ctx -> Type) -> Constraint
class Keep t where
    -- | 'keep' is often called @lift@, but we stick with 'Wk' terminology.
    -- One benefit is that the name 'keep' is less likely to clash.
    keep   :: t ctx ctx' -> t (S ctx) (S ctx')

-- | 'keep' 'IdxMapping' @arity@ times.
keepAdd
    :: Keep m
    => Add arity ctxA ctxA'
    -> m ctxA ctxB
    -> (forall ctxB'. Add arity ctxB ctxB' -> m ctxA' ctxB' -> r)
    -> r
keepAdd AZ     w kont = kont AZ w
keepAdd (AS a) w kont = keepAdd a w $ \a' w' -> kont (AS a') (keep w')

instance Keep Wk where
    keep = KeepWk

instance Keep Ren where
    keep = keepRen

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

-- | Contractions
class Contract t where
    contract :: Wk m n -> t n -> Maybe (t m)

instance Weaken Proxy where
     weaken _ _ = Proxy

instance Rename Proxy where
    rename _ _ = Proxy

instance Contract Proxy where
    contract _ _ = Just Proxy

instance Weaken Idx where
    weaken = weakenIdx

instance Rename Idx where
    rename = renameIdx

instance Contract Idx where
    contract = contractIdx

instance Weaken (Ren n) where
    weaken w (MkRen js) = MkRen (fmap (weaken w) js)

instance Rename (Ren n) where
    rename r r' = compRen r' r
