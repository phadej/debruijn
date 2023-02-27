{-# LANGUAGE Unsafe #-}
-- | de Bruijn levels for well-scoped terms.
module DeBruijn.Internal.Lvl (
    -- * Levels
    Lvl (UnsafeLvl),
    lvlToIdx,
    lvlZ,
    sinkLvl,
    Sinkable (..),
    sink,
    mapSink,
    sinkSize,
    mapSinkSize,
    sinkAdd,
    mapSinkAdd,
) where

import Data.Coerce   (coerce)
import Data.Kind     (Constraint, Type)
import Data.Proxy    (Proxy (..))
import Unsafe.Coerce (unsafeCoerce)

import DeBruijn.Add
import DeBruijn.Ctx
import DeBruijn.Internal.Idx
import DeBruijn.Internal.Size
import DeBruijn.Lte

-- $setup
-- >>> import DeBruijn
-- >>> import DeBruijn.Lte

-------------------------------------------------------------------------------
-- de Bruijn levels
-------------------------------------------------------------------------------

-- | de Bruijn levels.
type Lvl :: Ctx -> Type
type role Lvl nominal
newtype Lvl ctx = UnsafeLvl { _unLvl :: Int }
  deriving (Eq, Ord)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (Lvl ctx) where
    showsPrec d (UnsafeLvl i) = showsPrec d i

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

-- | Convert level to index.
--
-- >>> lvlToIdx S2 (lvlZ S1)
-- 0
--
lvlToIdx :: Size ctx -> Lvl ctx -> Idx ctx
lvlToIdx (UnsafeSize ctx) (UnsafeLvl lvl) = UnsafeIdx (ctx - lvl - 1)

-- | Last level.
--
-- >>> lvlZ S1
-- 1
--
-- >>> lvlZ S5
-- 5
--
lvlZ :: Size ctx -> Lvl (S ctx)
lvlZ (UnsafeSize s) = UnsafeLvl s

-- | Sink 'Lvl' into a larger context.
--
-- >>> sinkLvl (lvlZ S3)
-- 3
--
-- >>> sink (lvlZ S3)
-- 3
--
-- >>> mapLvl (LS LZ) (lvlZ S3)
-- 3
--
sinkLvl :: Lvl n -> Lvl (S n)
sinkLvl = coerce

-------------------------------------------------------------------------------
-- Sinkable
-------------------------------------------------------------------------------

-- | Sinkable terms can be weakened (sunk) cheaply.
type Sinkable :: (Ctx -> Type) -> Constraint
class Sinkable t where
    mapLvl :: Lte ctx ctx' -> t ctx -> t ctx'

instance Sinkable Lvl where mapLvl _ = coerce
instance Sinkable Proxy where mapLvl _ = coerce

-- | Sink term.
sink :: Sinkable t => t ctx -> t (S ctx)
sink = unsafeCoerce

-- | Sink term from empty context to a context of given size.
sinkSize :: Sinkable t => Size ctx -> t EmptyCtx -> t ctx
sinkSize _ = unsafeCoerce

-- | Essentially @'fmap' 'sink'@
mapSink :: (Functor f, Sinkable t) => f (t ctx) -> f (t (S ctx))
mapSink = unsafeCoerce

-- | Essentially @'fmap' . 'sinkSize'@
mapSinkSize :: (Functor f, Sinkable t) => Size ctx -> f (t EmptyCtx) -> f (t ctx)
mapSinkSize _ = unsafeCoerce

sinkAdd :: Sinkable t => Add n ctx ctx' -> t ctx -> t ctx'
sinkAdd _ = unsafeCoerce

mapSinkAdd :: (Functor f, Sinkable t) => Add n ctx ctx' -> f (t ctx) -> f (t ctx')
mapSinkAdd _ = unsafeCoerce
