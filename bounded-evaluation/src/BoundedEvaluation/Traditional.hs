module BoundedEvaluation.Traditional (
    eval,
    conv,
) where

import Data.Function (fix)

import BoundedEvaluation.Base
import BoundedEvaluation.Term

-- $setup
--
-- >>> import BoundedEvaluation.Base
-- >>> import BoundedEvaluation.Term

-------------------------------------------------------------------------------
-- Values
-------------------------------------------------------------------------------

-- | Evaluation environment.
type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (VTerm ctx')

-- | Closure, a term to be evaluated, but which needs an extra value.
type Closure :: Ctx -> Type
data Closure ctx' where Closure :: EvalEnv ctx ctx' -> Term (S ctx) -> Closure ctx'
deriving instance Show (Closure ctx)

type VTerm :: Ctx -> Type
data VTerm ctx where
    VLam :: Closure ctx -> VTerm ctx
    VErr :: String -> VTerm ctx
    VNeu :: Lvl ctx -> Spine ctx -> VTerm ctx
    VZer :: VTerm ctx
    VSuc :: VTerm ctx -> VTerm ctx

type Spine :: Ctx -> Type
data Spine ctx
    = VNil
    | VApp !(Spine ctx) (VTerm ctx)
    | VMch !(Spine ctx) (VTerm ctx) (Closure ctx)

deriving instance Show (VTerm ctx)
deriving instance Show (Spine ctx)

instance Sinkable VTerm where mapLvl = error "TODO"

-------------------------------------------------------------------------------
-- Evaluation
-------------------------------------------------------------------------------

-- | Evaluation
--
-- >>> eval EmptyEnv ex1
-- VSuc (VSuc (VSuc (VSuc (VSuc (VSuc VZer)))))
--
-- >>> eval EmptyEnv ex2
-- VSuc (VSuc (VSuc (VSuc (VSuc (VSuc VZer)))))
--
-- >>> take 60 $ show $ eval EmptyEnv ex3
-- "VSuc (VSuc (VSuc (VSuc (VSuc (VSuc (VSuc (VSuc (VSuc (VSuc ("
--
eval :: EvalEnv ctx ctx' -> Term ctx -> VTerm ctx'
eval env (Var x)     = lookupEnv x env
eval env (Lam t)     = VLam (Closure env t)
eval env (App f t)   = vApp (eval env f) (eval env t)
eval _   Zer         = VZer
eval env (Suc t)     = VSuc (eval env t)
eval env (Mch t z s) = vMch (eval env t) (eval env z) (Closure env s)
eval env (Let t e)   = eval (env :> eval env t) e
eval env (Fix t)     = fix (\v -> eval (env :> v) t)

vApp :: VTerm ctx -> VTerm ctx -> VTerm ctx
vApp (VLam (Closure env f)) t = eval (env :> t) f
vApp (VNeu l sp)            t = VNeu l (VApp sp t)
vApp (VErr err)             _ = VErr err
vApp VZer {}                _ = VErr "applying to zero"
vApp VSuc {}                _ = VErr "applying to succ"

vMch :: VTerm ctx -> VTerm ctx -> Closure ctx -> VTerm ctx
vMch VZer z _ = z
vMch (VSuc t) _ (Closure env s) = eval (env :> t) s
vMch (VNeu l sp) z s = VNeu l (VMch sp z s)
vMch (VErr err)             _ _ = VErr err
vMch VLam {} _ _ = VErr "splitting lambda"

run1 :: Size ctx -> Closure ctx -> VTerm (S ctx)
run1 s (Closure env t) = eval (mapSink env :> VNeu (lvlZ s) VNil) t

-------------------------------------------------------------------------------
-- Conversion checking
-------------------------------------------------------------------------------

-- | Conversion check
--
-- >>> conv SZ (eval EmptyEnv ex1) (eval EmptyEnv ex2)
-- True
--
-- As long as either argument is finite,
-- conversion function will terminate:
--
-- >>> conv SZ (eval EmptyEnv ex1) (eval EmptyEnv ex3)
-- False
--
-- Note: we have to be careful when conversion checking things with @fix@
-- For example if we compare @ind@ with itself, it will loop,
-- as the structure (due 'fix') is indeed infinite.
--
conv :: Size ctx -> VTerm ctx -> VTerm ctx -> Bool
conv _ VZer          VZer          = True
conv _ VZer          _             = False
conv s (VSuc n1)     (VSuc n2)     = conv s n1 n2
conv _ (VSuc _)      _             = False
conv s (VLam c1)     (VLam c2)     = conv (SS s) (run1 s c1) (run1 s c2)
conv _ (VLam _)      _             = False
conv s (VNeu l1 sp1) (VNeu l2 sp2) = l1 == l2 && convSpine s sp1 sp2
conv _ (VNeu _ _)    _             = False
conv _ (VErr _)      _             = False

convSpine :: Size ctx -> Spine ctx -> Spine ctx -> Bool
convSpine _ VNil             VNil             = True
convSpine _ VNil             _                = False
convSpine s (VApp sp1 t1)    (VApp sp2 t2)    = convSpine s sp1 sp2 && conv s t1 t2
convSpine _ (VApp _ _)       _                = False
convSpine s (VMch sp1 z1 s1) (VMch sp2 z2 s2) = convSpine s sp1 sp2 && conv s z1 z2 && conv (SS s) (run1 s s1) (run1 s s2)
convSpine _ (VMch _ _ _)     _                = False
