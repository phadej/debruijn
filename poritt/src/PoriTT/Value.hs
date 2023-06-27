module PoriTT.Value (
    -- * Values
    VTerm (..),
    VElim (..),
    Spine (..),
    -- ** Closure
    Closure (..),
    ClosureE,
    ClosureT,
    valZ,
    -- ** Evaluation context
    EvalEnv,
    EvalEnv',
    EvalElim (..),
    emptyEvalEnv,
    emptyEvalEnv',
    -- ** Evaluation error
    EvalError (..),
    -- * Staging values
    STerm (..),
    SElim (..),
    svalZ,
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
    | EvalErrorStg  -- ^ error in staging.
  deriving Show

-------------------------------------------------------------------------------
-- VTerm and VElim
-------------------------------------------------------------------------------

-- | Semantic term
type VTerm :: Ctx -> Type
data VTerm ctx where
    VPie :: !Name -> (VTerm ctx) -> !(ClosureT ctx) -> VTerm ctx
    VLam :: !Name -> !(ClosureT ctx)  -> VTerm ctx
    VUni :: VTerm ctx
    VDsc :: VTerm ctx
    VDe1 :: VTerm ctx
    VDeS :: VTerm ctx -> VTerm ctx -> VTerm ctx
    VDeX :: VTerm ctx -> VTerm ctx
    VMuu :: VTerm ctx -> VTerm ctx
    VCon :: VTerm ctx -> VTerm ctx
    VSgm :: !Name -> (VTerm ctx) -> !(ClosureT ctx) -> VTerm ctx
    VMul :: VTerm ctx -> VTerm ctx -> VTerm ctx
    VLbl :: !Label -> VTerm ctx
    VFin :: !(Set Label) -> VTerm ctx
    VCod :: VTerm ctx -> VTerm ctx
    VQuo :: STerm ctx -> VTerm ctx -> VTerm ctx -- we preserve the syntax, but also evalute.
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
    mapLvl f (VQuo t t')   = VQuo (mapLvl f t) (mapLvl f t')
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

-- Terms in context
type EvalElim :: Ctx -> Type
data EvalElim ctx
    = VElim (VElim ctx)
    | SElim (SElim ctx)

deriving instance Show (EvalElim ctx)

instance Sinkable EvalElim where
    mapLvl f (VElim e) = VElim (mapLvl f e)
    mapLvl f (SElim e) = SElim (mapLvl f e)

type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (VElim ctx')

type EvalEnv' :: Ctx -> Ctx -> Type
type EvalEnv' ctx ctx' = Env ctx (EvalElim ctx')

emptyEvalEnv :: EvalEnv EmptyCtx EmptyCtx
emptyEvalEnv = EmptyEnv

emptyEvalEnv' :: EvalEnv' EmptyCtx EmptyCtx
emptyEvalEnv' = EmptyEnv

type Closure :: (Ctx -> Type) -> Ctx -> Type
data Closure term ctx' where Closure :: EvalEnv' ctx ctx' -> term (S ctx) -> Closure term ctx'

deriving instance (forall ctx'. Show (term ctx')) => Show (Closure term ctx)

type ClosureE = Closure Elim
type ClosureT = Closure Term

instance Sinkable (Closure term) where
    mapLvl f (Closure env t) = Closure (fmap (mapLvl f) env) t

valZ :: Size ctx -> VElim (S ctx)
valZ s = VNeu (lvlZ s) VNil

-------------------------------------------------------------------------------
-- Symbolic terms
-------------------------------------------------------------------------------

type STerm :: Ctx -> Type
data STerm ctx where
    SPie :: !Name -> STerm ctx -> !(ClosureT ctx) -> STerm ctx
    SLam :: !Name -> !(ClosureT ctx) -> STerm ctx
    SSgm :: !Name -> STerm ctx -> !(ClosureT ctx) -> STerm ctx
    SMul :: STerm ctx -> STerm ctx -> STerm ctx
    SLbl :: Label -> STerm ctx
    SFin :: Set Label -> STerm ctx
    SUni :: STerm ctx
    SDsc :: STerm ctx
    SDe1 :: STerm ctx
    SDeS :: STerm ctx -> STerm ctx -> STerm ctx
    SDeX :: STerm ctx -> STerm ctx
    SMuu :: STerm ctx -> STerm ctx
    SCon :: STerm ctx -> STerm ctx
    SCod :: STerm ctx -> STerm ctx
    SQuo :: STerm ctx -> STerm ctx
    SEmb :: SElim ctx -> STerm ctx
    SVal :: VTerm ctx -> STerm ctx

type SElim :: Ctx -> Type
data SElim ctx where
    SErr :: EvalError -> SElim ctx
    SVar :: Lvl ctx -> SElim ctx
    SGbl :: Global -> SElim ctx
    SApp :: SElim ctx -> STerm ctx -> SElim ctx
    SSel :: SElim ctx -> Selector -> SElim ctx
    SSwh :: SElim ctx -> STerm ctx -> Map Label (STerm ctx) -> SElim ctx
    SDeI :: SElim ctx -> STerm ctx -> STerm ctx -> STerm ctx -> STerm ctx -> SElim ctx
    SInd :: SElim ctx -> STerm ctx -> STerm ctx -> SElim ctx
    SAnn :: STerm ctx -> STerm ctx -> SElim ctx
    SLet :: !Name -> SElim ctx -> !(ClosureE ctx) -> SElim ctx
    SSpl :: SElim ctx -> SElim ctx

deriving instance Show (STerm ctx)
deriving instance Show (SElim ctx)

instance Sinkable STerm where
    mapLvl f (SPie x a b)  = SPie x (mapLvl f a) (mapLvl f b)
    mapLvl f (SLam x clos) = SLam x (mapLvl f clos)
    mapLvl f (SSgm x a b)  = SSgm x (mapLvl f a) (mapLvl f b)
    mapLvl f (SMul t s)    = SMul (mapLvl f t) (mapLvl f s)
    mapLvl _ SUni          = SUni
    mapLvl _ SDsc          = SDsc
    mapLvl _ SDe1          = SDe1
    mapLvl f (SDeS t r)    = SDeS (mapLvl f t) (mapLvl f r)
    mapLvl f (SDeX t)      = SDeX (mapLvl f t)
    mapLvl _ (SLbl l)      = SLbl l
    mapLvl _ (SFin ls)     = SFin ls
    mapLvl f (SMuu a)      = SMuu (mapLvl f a)
    mapLvl f (SCon a)      = SCon (mapLvl f a)
    mapLvl f (SCod a)      = SCod (mapLvl f a)
    mapLvl f (SQuo t)      = SQuo (mapLvl f t)
    mapLvl f (SEmb e)      = SEmb (mapLvl f e)
    mapLvl f (SVal e)      = SVal (mapLvl f e)

instance Sinkable SElim where
    mapLvl _ (SErr err)       = SErr err
    mapLvl f (SVar x)         = SVar (mapLvl f x)
    mapLvl _ (SGbl g)         = SGbl g
    mapLvl f (SApp g t)       = SApp (mapLvl f g) (mapLvl f t)
    mapLvl f (SSel e t)       = SSel (mapLvl f e) t
    mapLvl f (SSwh xs m rs)   = SSwh (mapLvl f xs) (mapLvl f m) (fmap (mapLvl f) rs)
    mapLvl f (SInd e m t)     = SInd (mapLvl f e) (mapLvl f m) (mapLvl f t)
    mapLvl f (SDeI e m x y z) = SDeI (mapLvl f e) (mapLvl f m) (mapLvl f x) (mapLvl f y) (mapLvl f z)
    mapLvl f (SSpl e)         = SSpl (mapLvl f e)
    mapLvl f (SLet x a b)     = SLet x (mapLvl f a) (mapLvl f b)
    mapLvl f (SAnn t s)       = SAnn (mapLvl f t) (mapLvl f s)

svalZ :: Size ctx -> SElim (S ctx)
svalZ s = SVar (lvlZ s)
