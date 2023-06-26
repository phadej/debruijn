module PoriTT.Eval (
    -- * Types
    VTerm (..),
    VElim (..),
    Spine (..),
    -- ** Closure
    Closure (..),
    run,
    runZ,
    valZ,
    -- * Evaluation
    evalTerm,
    evalElim,
    EvalError (..),
    force,
    -- ** Evaluation context
    EvalEnv,
    emptyEvalEnv,
    -- ** Eliminations
    vapp,
    vapps,
    vsel,
    vswh,
    vdei,
    vind,
    vemb,
    vspl,
    -- ** Smart constructors
    vann,
    varr,
    vgbl,
) where

import qualified Data.Map.Lazy as Map

import PoriTT.Base
import PoriTT.Global
import PoriTT.Name
import PoriTT.Nice
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

import {-# SOURCE #-} PoriTT.Builtins (allTermGlobal)

-------------------------------------------------------------------------------
-- VTerm and VElim
-------------------------------------------------------------------------------

-- | Force globals, when we need to pattern match on types.
force :: VTerm ctx -> VTerm ctx
force (VEmb (VGbl _ _ v)) = force (vemb v)
force v                   = v

-------------------------------------------------------------------------------
-- Closure
-------------------------------------------------------------------------------

run :: Size ctx -> Closure ctx -> VElim ctx -> VTerm ctx
run s (Closure env f) t = evalTerm s (env :> t) f

-- | Run closure with (neutral) variable as an argument.
runZ :: Size ctx -> Closure ctx -> VTerm (S ctx)
runZ s clos = run (SS s) (sink clos) (valZ s)

-------------------------------------------------------------------------------
-- Evaluation
-------------------------------------------------------------------------------

evalTerm :: Size ctx' -> EvalEnv ctx ctx' -> Term ctx -> VTerm ctx'
evalTerm _ env (Lam x t)   = VLam x (Closure env t)
evalTerm _ _   Uni         = VUni
evalTerm _ _   Dsc         = VDsc
evalTerm _ _   De1         = VDe1
evalTerm s env (DeS t r)   = VDeS (evalTerm s env t) (evalTerm s env r)
evalTerm s env (DeX t)     = VDeX (evalTerm s env t)
evalTerm s env (Muu t)     = VMuu (evalTerm s env t)
evalTerm s env (Con t)     = VCon (evalTerm s env t)
evalTerm s env (Pie x a b) = VPie x (evalTerm s env a) (Closure env b)
evalTerm s env (Sgm x a b) = VSgm x (evalTerm s env a) (Closure env b)
evalTerm s env (Emb e)     = vemb (evalElim s env e)
evalTerm _ _   (Lbl l)     = VLbl l
evalTerm _ _   (Fin ls)    = VFin ls
evalTerm s env (Mul t r)   = VMul (evalTerm s env t) (evalTerm s env r)
evalTerm s env (Cod a)     = VCod (evalTerm s env a)
evalTerm s env (Quo t)     = vquo (evalTerm s env t)
evalTerm s env (WkT w t)   = evalTerm s (weakenEnv w env) t


evalElim :: Size ctx' -> EvalEnv ctx ctx' -> Elim ctx -> VElim ctx'
evalElim _ env (Var x)         = lookupEnv x env
evalElim s _   (Gbl g)         = vgbl s g
evalElim s env (Ann t a)       = vann (evalTerm s env t) (evalTerm s env a)
evalElim s env (App f t)       = vapp s (evalElim s env f) (evalTerm s env t)
evalElim s env (Sel e z)       = vsel s (evalElim s env e) z
evalElim s env (Swh e m ts)    = vswh s (evalElim s env e) (evalTerm s env m) (fmap (evalTerm s env) ts)
evalElim s env (DeI e m x y z) = vdei s (evalElim s env e) (evalTerm s env m) (evalTerm s env x) (evalTerm s env y) (evalTerm s env z)
evalElim s env (Ind e m t)     = vind s (evalElim s env e) (evalTerm s env m) (evalTerm s env t)
evalElim s env (Spl e)         = vspl s (evalElim s env e)
evalElim s env (Let _ t r)     = evalElim s (env :> evalElim s env t) r
evalElim s env (WkE w e)       = evalElim s (weakenEnv w env) e

-------------------------------------------------------------------------------
-- Eliminations
-------------------------------------------------------------------------------

varr :: VTerm ctx -> Term Ctx1 -> VTerm ctx
varr a b = VPie "_" a (Closure EmptyEnv b)

vemb :: VElim ctx -> VTerm ctx
vemb (VAnn t _) = t
vemb e          = VEmb e

-- this reduction is not confluent, but we make more progress using
-- it -- and equate more things.
vann :: VTerm ctx -> VTerm ctx -> VElim ctx
vann (VEmb e) _ = e
vann t        s = VAnn t s

vgbl :: Size ctx -> Global -> VElim ctx
vgbl s g = VGbl g VNil (sinkSize s (gblVal g))

vapp :: Size ctx -> VElim ctx -> VTerm ctx -> VElim ctx
vapp s (VAnn (VLam _ clos) (force -> VPie _ a b)) t =
    let t' = vann t a
    in vann (run s clos t') (run s b t')

vapp s (VAnn (VEmb e) _) t = vapp s e t
vapp _ (VAnn _ _)        _ = VErr EvalErrorApp
vapp _ (VNeu l sp)       t = VNeu l (VApp sp t)
vapp s (VGbl g sp h)     t = VGbl g (VApp sp t) (vapp s h t)
vapp _ (VErr msg)        _ = VErr msg

vapps :: Size ctx -> VElim ctx -> [VTerm ctx] -> VElim ctx
vapps s f xs = foldl' (vapp s) f xs

vsel :: Size ctx -> VElim ctx -> Selector -> VElim ctx
vsel s (VAnn (VMul t r) (force -> VSgm _ a b)) z
    | z == "fst"       = vann t a
    | z == "snd"       = vann r (run s b (vann t a))
    | otherwise        = VErr EvalErrorSel

vsel s (VAnn (VEmb e) _) z = vsel s e z
vsel _ (VAnn _ _)        _ = VErr EvalErrorSel
vsel _ (VNeu l sp)       t = VNeu l (VSel sp t)
vsel s (VGbl g sp h)     t = VGbl g (VSel sp t) (vsel s h t)
vsel _ (VErr msg)        _ = VErr msg

vswh :: Size ctx -> VElim ctx -> VTerm ctx -> Map Label (VTerm ctx) -> VElim ctx
vswh s (VAnn (VLbl l) ty@(force -> VFin _)) m ts = case Map.lookup l ts of
    Just t -> vann t $ vemb $ vapp s (vann m (varr ty Uni)) (VLbl l)
    Nothing -> VErr EvalErrorSwh
vswh s (VAnn (VEmb e) _) m ts = vswh s e m ts
vswh _ (VAnn _ _)        _ _  = VErr EvalErrorSwh
vswh _ (VNeu l sp)       m ts = VNeu l (VSwh sp m ts)
vswh s (VGbl g sp h)     m ts = VGbl g (VSwh sp m ts) (vswh s h m ts)
vswh _ (VErr msg)        _ _  = VErr msg

vdei :: Size ctx -> VElim ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> VElim ctx
-- indDesc `1       M 1ₘ Σₘ Xₘ    = 1ₘ
vdei s (VAnn VDe1 (force -> VDsc)) m x _ _ = do
    let m' = vann m $ varr VDsc Uni
    let x' = vann x $ evalTerm s (EmptyEnv :> m') descIndMotive1
    x'
-- indDesc (`Σ S D) M 1ₘ Σₘ Xₘ    = Σₘ S D (λ s → indDesc (D s) M 1ₘ Σₘ Xₘ)
vdei s (VAnn (VDeS t r) (force -> VDsc)) m x y z = do
    let m' = vann m $ varr VDsc Uni
    let x' = vann x $ evalTerm s (EmptyEnv :> m') descIndMotive1
    let y' = vann y $ evalTerm s (EmptyEnv :> m') descIndMotiveS
    let z' = vann z $ evalTerm s (EmptyEnv :> m') descIndMotiveX
    let r' = vann r $ varr t Dsc
    vapps s y' [t, r, VLam "s" $ Closure (EmptyEnv :> m' :> x' :> y' :> z' :> r') $ Emb $ DeI (var I1 @@ var IZ) (var I5) (var I4) (var I3) (var I2) ]

-- indDesc (`X D)   M 1ₘ Σₘ Xₘ    = Xₘ D (indDesc D M 1ₘ Σₘ Xₘ)
vdei s (VAnn (VDeX t) (force -> VDsc)) m x y z = do
    let m' = vann m $ varr VDsc Uni
    let z' = vann z $ evalTerm s (EmptyEnv :> m') descIndMotiveX
    vapps s z' [t, vemb $ vdei s (vann t VDsc) m x y z]

vdei s (VAnn (VEmb e) _) m x y z = vdei s e m x y z
vdei _ (VAnn _ _)        _ _ _ _ = VErr EvalErrorDeI
vdei _ (VNeu l sp)       m x y z = VNeu l (VDeI sp m x y z)
vdei s (VGbl g sp h)     m x y z = VGbl g (VDeI sp m x y z) (vdei s h m x y z)
vdei _ (VErr msg)        _ _ _ _ = VErr msg

vind :: Size ctx -> VElim ctx -> VTerm ctx -> VTerm ctx -> VElim ctx
-- ind : {D : Desc}
--     → (x : μ D)
--     → (M : μ D → Set)
--     → (conₘ : (d : ⟦ D ⟧ (μ D)) → All D (μ D) M d → M (con d))
--     →  M x
-- ind {D} (con d) M conₘ = conₘ d (all D (μ D) M (λ x → ind x M conₘ) d)
vind s (VAnn (VCon d) (force -> VMuu dd)) m c = do
    let m'  = vann m  $ varr (VMuu d) Uni
    let dd' = vann dd VDsc
    let d'  = vann d TODO
    let c'  = vann c $ evalTerm s (EmptyEnv :> dd' :> m') muMotiveT
    evalElim s (EmptyEnv :> dd' :> m' :> d' :> c') $
        var IZ @@ var I1 @@ (Gbl allTermGlobal @@ var I3 @@ Muu (var I3) @@ var I2 @@ Lam "x" (Emb (Ind (var IZ) (var I3) (var I1))) @@ var I1)

vind s (VAnn (VEmb e) _) m t = vind s e m t
vind _ (VAnn _ _)       _ _ = VErr EvalErrorInd
vind _ (VNeu l sp)      m t = VNeu l (VInd sp m t)
vind s (VGbl g sp h)    m t = VGbl g (VInd sp m t) (vind s h m t)
vind _ (VErr msg)       _ _ = VErr msg

vspl :: Size ctx -> VElim ctx -> VElim ctx
vspl _ (VAnn (VQuo t) (force -> VCod a)) = vann t a

vspl s (VAnn (VEmb e) _)                 = vspl s e
vspl _ (VAnn _ _)                        = VErr EvalErrorSpl
vspl _ (VNeu l sp)                       = VNeu l (VSpl sp)
vspl s (VGbl g sp h)                     = VGbl g (VSpl sp) (vspl s h)
vspl _ (VErr msg)                        = VErr msg

vquo :: VTerm ctx -> VTerm ctx
vquo = VQuo

{-
vquo (VEmb e) = vemb (vquo' e)

vquo' :: VElim ctx -> VElim ctx
vquo' (VNeu l (VSpl sp))   = VNeu l sp
vquo' (VGbl g (VSpl sp) h) = VGbl g sp (vquo' h)
vquo' e                    = ?

-}