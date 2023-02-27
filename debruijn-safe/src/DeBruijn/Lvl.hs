{-# LANGUAGE Safe #-}
module DeBruijn.Lvl (
    Lvl,
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

import Data.Kind (Constraint, Type)

import DeBruijn.Add
import DeBruijn.Ctx
import DeBruijn.Idx
import DeBruijn.Lte
import DeBruijn.Size

-- $setup
-- >>> import DeBruijn
-- >>> import DeBruijn.Lte

-------------------------------------------------------------------------------
-- de Bruijn levels
-------------------------------------------------------------------------------

-- | de Bruijn levels.
--
--
type Lvl :: Ctx -> Type
type role Lvl nominal
data Lvl ctx = MkLvl !Int !(Idx ctx)
  deriving (Eq, Ord)

-- Note: we need an integer field for Show instance.

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show (Lvl ctx) where
    showsPrec d (MkLvl i _) = showsPrec d i

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

-- | Convert level to index.
--
-- >>> lvlToIdx S2 (lvlZ S1)
-- 0
--
lvlToIdx :: Size ctx -> Lvl ctx -> Idx ctx
lvlToIdx _ (MkLvl _ x) = x

-- | Last level.
--
-- >>> lvlZ S1
-- 1
--
-- >>> lvlZ S5
-- 5
--
lvlZ :: Size ctx -> Lvl (S ctx)
lvlZ s = MkLvl (sizeToInt s) IZ

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
--
sinkLvl :: Lvl ctx -> Lvl (S ctx)
sinkLvl (MkLvl s i) = MkLvl s (IS i)

-------------------------------------------------------------------------------
-- Sinkable
-------------------------------------------------------------------------------

-- | Sinkable terms can be weakened (sunk) cheaply.
-- (when 'Lvl' is implemented as newtype over 'Int').
type Sinkable :: (Ctx -> Type) -> Constraint
class Sinkable t where
    mapLvl :: Lte ctx ctx' -> t ctx -> t ctx'

lteLvl :: Lte ctx ctx' -> Lvl ctx -> Lvl ctx'
lteLvl LZ     t           = t
lteLvl (LS l) (MkLvl s i) = MkLvl s (lteIdx (LS l) i)

lteIdx :: Lte ctx ctx' -> Idx ctx -> Idx ctx'
lteIdx LZ     i = i
lteIdx (LS s) i = IS (lteIdx s i)

instance Sinkable Lvl where mapLvl = lteLvl

sink :: Sinkable t => t ctx -> t (S ctx)
sink = mapLvl (LS LZ)

mapSink :: (Functor f, Sinkable t) => f (t ctx) -> f (t (S ctx))
mapSink = fmap sink

sinkSize :: Sinkable t => Size ctx -> t EmptyCtx -> t ctx
sinkSize SZ     t = t
sinkSize (SS n) t = sink (sinkSize n t)

mapSinkSize :: (Functor f, Sinkable t) => Size ctx -> f (t EmptyCtx) -> f (t ctx)
mapSinkSize = fmap . sinkSize

sinkAdd :: Sinkable t => Add n ctx ctx' -> t ctx -> t ctx'
sinkAdd AZ t = t
sinkAdd (AS s) t = sink (sinkAdd s t)

mapSinkAdd :: (Functor f, Sinkable t) => Add n ctx ctx' -> f (t ctx) -> f (t ctx')
mapSinkAdd = fmap . sinkAdd
