module PoriTT.Value (
    -- * Types
    VTerm (..),
    VElim (..),
    Spine (..),
    -- ** Closure
    Closure (..),
    valZ,
    -- ** Evaluation context
    EvalEnv,
    emptyEvalEnv,
    -- ** Evaluation error
    EvalError (..),
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.Term

import {-# SOURCE #-} PoriTT.Global (Global)

-------------------------------------------------------------------------------
-- Evaluation errors
-------------------------------------------------------------------------------

-- | Evaluation error.
--
-- These shouldn't happen if we evaluate type-correct code.
--
data EvalError
    = EvalErrorApp  -- ^ error in function application
    | EvalErrorSel  -- ^ error in selector application
    | EvalErrorSwh  -- ^ error in @switch@
    | EvalErrorDeI  -- ^ error in @indDesc@
    | EvalErrorInd  -- ^ error in @ind@
    | EvalErrorSpl  -- ^ error in @spl@
  deriving Show

-------------------------------------------------------------------------------
-- VTerm and VElim
-------------------------------------------------------------------------------

-- | Semantic term
type VTerm :: Ctx -> Type
data VTerm ctx where
    VPie :: !Name -> (VTerm ctx) -> !(Closure ctx) -> VTerm ctx
    VLam :: !Name -> !(Closure ctx)  -> VTerm ctx
    VUni :: VTerm ctx
    VDsc :: VTerm ctx
    VDe1 :: VTerm ctx
    VDeS :: VTerm ctx -> VTerm ctx -> VTerm ctx
    VDeX :: VTerm ctx -> VTerm ctx
    VMuu :: VTerm ctx -> VTerm ctx
    VCon :: VTerm ctx -> VTerm ctx
    VSgm :: !Name -> (VTerm ctx) -> !(Closure ctx) -> VTerm ctx
    VMul :: VTerm ctx -> VTerm ctx -> VTerm ctx
    VLbl :: !Label -> VTerm ctx
    VFin :: !(Set Label) -> VTerm ctx
    VCod :: VTerm ctx -> VTerm ctx
    VQuo :: VTerm ctx -> VTerm ctx
    VEmb :: VElim ctx -> VTerm ctx  -- no VAnn

-- | Semantic elimination
type VElim :: Ctx -> Type
data VElim ctx where
    VErr :: EvalError -> VElim ctx
    VAnn :: VTerm ctx -> VTerm ctx -> VElim ctx
    VGbl :: !Global -> !(Spine ctx) -> VElim ctx -> VElim ctx
    VNeu :: Lvl ctx -> Spine ctx -> VElim ctx

deriving instance Show (VTerm ctx)
deriving instance Show (VElim ctx)

instance Sinkable VTerm where
    mapLvl _ VUni          = VUni
    mapLvl _ VDsc          = VDsc
    mapLvl _ VDe1          = VDe1
    mapLvl f (VDeS t s)    = VDeS (mapLvl f t) (mapLvl f s)
    mapLvl f (VDeX t)      = VDeX (mapLvl f t)
    mapLvl f (VMuu t)      = VMuu (mapLvl f t)
    mapLvl f (VCon t)      = VCon (mapLvl f t)
    mapLvl f (VLam x clos) = VLam x (mapLvl f clos)
    mapLvl f (VPie x a b)  = VPie x (mapLvl f a) (mapLvl f b)
    mapLvl f (VSgm x a b)  = VSgm x (mapLvl f a) (mapLvl f b)
    mapLvl f (VMul t s)    = VMul (mapLvl f t) (mapLvl f s)
    mapLvl _ (VLbl l)      = VLbl l
    mapLvl _ (VFin ls)     = VFin ls
    mapLvl f (VCod a)      = VCod (mapLvl f a)
    mapLvl f (VQuo t)      = VQuo (mapLvl f t)
    mapLvl f (VEmb e)      = VEmb (mapLvl f e)

instance Sinkable VElim where
    mapLvl _ (VErr msg)    = VErr msg
    mapLvl f (VNeu l sp)   = VNeu (mapLvl f l) (mapLvl f sp)
    mapLvl f (VGbl g sp t) = VGbl g (mapLvl f sp) (mapLvl f t)
    mapLvl f (VAnn t s)    = VAnn (mapLvl f t) (mapLvl f s)

-------------------------------------------------------------------------------
-- Spine
-------------------------------------------------------------------------------

-- | Spine of neutral terms ('VNeu').
type Spine :: Ctx -> Type
data Spine ctx
    = VNil
    | VApp !(Spine ctx) (VTerm ctx)
    | VSel !(Spine ctx) !Selector
    | VSwh !(Spine ctx) (VTerm ctx) !(Map Label (VTerm ctx)) -- Note: motive is lazy as we don't evaluate it. It's needed for type-checking only.
    | VDeI !(Spine ctx) (VTerm ctx) (VTerm ctx) (VTerm ctx) (VTerm ctx)
    | VInd !(Spine ctx) (VTerm ctx) (VTerm ctx)
    | VSpl !(Spine ctx)
  deriving Show

instance Sinkable Spine where
    mapLvl _ VNil              = VNil
    mapLvl f (VApp xs x)       = VApp (mapLvl f xs) (mapLvl f x)
    mapLvl f (VSel xs s)       = VSel (mapLvl f xs) s
    mapLvl f (VSwh xs m rs)    = VSwh (mapLvl f xs) (mapLvl f m) (fmap (mapLvl f) rs)
    mapLvl f (VDeI xs m x y z) = VDeI (mapLvl f xs) (mapLvl f m) (mapLvl f x) (mapLvl f y) (mapLvl f z)
    mapLvl f (VInd xs m t)     = VInd (mapLvl f xs) (mapLvl f m) (mapLvl f t)
    mapLvl f (VSpl xs)         = VSpl (mapLvl f xs)

-------------------------------------------------------------------------------
-- Closure
-------------------------------------------------------------------------------

type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (VElim ctx')

emptyEvalEnv :: EvalEnv EmptyCtx EmptyCtx
emptyEvalEnv = EmptyEnv

type Closure :: Ctx -> Type
data Closure ctx' where Closure :: EvalEnv ctx ctx' -> Term (S ctx) -> Closure ctx'

deriving instance Show (Closure ctx)

instance Sinkable Closure where
    mapLvl f (Closure env t) = Closure (fmap (mapLvl f) env) t

valZ :: Size ctx -> VElim (S ctx)
valZ s = VNeu (lvlZ s) VNil
