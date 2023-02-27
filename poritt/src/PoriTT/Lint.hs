-- | By lint we mean re-typechecking of core terms.
module PoriTT.Lint (
    LintCtx,
    emptyLintCtx,
    lintCheck,
    lintInfer,
) where

import qualified Data.Map as Map
import qualified Data.Set as Set

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Term
import PoriTT.Used

-------------------------------------------------------------------------------
-- Linting context
-------------------------------------------------------------------------------

data LintCtx ctx ctx' = LintCtx
    { values :: EvalEnv ctx ctx'
    , types  :: Env ctx (VTerm ctx')
    , types' :: Env ctx' (VTerm ctx')
    , names  :: Env ctx Name
    , names' :: Env ctx' Name
    , nscope :: NameScope
    , size   :: Size ctx'
    , doc    :: ![Doc]
    }

sinkLintCtx :: Name -> VTerm ctx' -> LintCtx ctx ctx' -> LintCtx ctx (S ctx')
sinkLintCtx x' t' (LintCtx vs ts ts' xs xs' ns s pp) = LintCtx (mapSink vs) (mapSink ts) (mapSink ts' :> sink t') xs (xs' :> x') ns (SS s) pp

emptyLintCtx :: NameScope -> LintCtx EmptyCtx EmptyCtx
emptyLintCtx ns = LintCtx EmptyEnv EmptyEnv EmptyEnv EmptyEnv EmptyEnv ns SZ []

bind :: LintCtx ctx ctx' -> Name -> Name -> VTerm ctx' -> LintCtx (S ctx) (S ctx')
bind ctx x x' a = bind' (sinkLintCtx x' a ctx) x (valZ (size ctx)) (sink a)

bind' :: LintCtx ctx ctx' -> Name -> VElim ctx' -> VTerm ctx' -> LintCtx (S ctx) ctx'
bind' (LintCtx vs ts ts' xs xs' ns s pp) x v t = LintCtx (vs :> v) (ts :> t) ts' (xs :> x) xs' ns s pp

weakenLintCtx :: Wk ctx ctx' -> LintCtx ctx' ctx'' -> LintCtx ctx ctx''
weakenLintCtx w (LintCtx vs ts ts' xs xs' ns s pp) = LintCtx (weakenEnv w vs) (weakenEnv w ts) ts' (weakenEnv w xs) xs' ns s pp

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

lintError :: LintCtx ctx ctx' -> Doc -> [Doc] -> Either String a
lintError ctx msg extras = Left $ ppRender False $ ppHanging
    ("LINT:" <+> msg)
    [ "*" <+> e
    | e <- extras ++ doc ctx
    ]

prettyVTermCtx :: LintCtx ctx ctx' -> VTerm ctx' -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names'

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

lintCheck
    :: LintCtx ctx ctx'           -- ^ Elaboration context
    -> Term ctx                   -- ^ Term
    -> VTerm ctx'                 -- ^ Expected type
    -> Either String ()
lintCheck ctx t a = do
    let d = "When checking that" <+> prettyTerm ctx.nscope ctx.names 0 t <+> "has type" <+> prettyVTermCtx ctx a
    lintCheck' ctx { doc = d : doc ctx } t a

lintInfer :: LintCtx ctx ctx' -> Elim ctx -> Either String (VTerm ctx')
lintInfer ctx e = do
    let d = "When infering type of" <+> prettyElim ctx.nscope ctx.names 0 e
    lintInfer' ctx { doc = d : doc ctx } e

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

lintCheck' :: LintCtx ctx ctx' -> Term ctx -> VTerm ctx' -> Either String ()
lintCheck' ctx (Lam x t)   (force -> VPie y a b) = do
    --
    --  x : A ⊢ B ∋ t
    -- --------------------------------- lam
    --        ⊢ Π (x : A) → B ∋ λ x → t
    --
    let ctx' = bind ctx x y a
    lintCheck ctx' t (runZ ctx.size b)
lintCheck' ctx (Lam _ _)   ty   =
    lintError ctx "Lambda abstraction should have function type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (Pie x a b) (force -> VUni) = do
    --
    --        ⊢ U ∋ A
    --  x : A ⊢ U ∋ B
    -- --------------------------- pi
    --        ⊢ U ∋ Π (x : A) → B
    --
    lintCheck ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    lintCheck (bind ctx x x a') b VUni
lintCheck' ctx (Pie _ _ _) ty =
    lintError ctx "forall type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
lintCheck' ctx (Sgm x a b) (force -> VUni) = do
    --
    --        ⊢ U ∋ A
    --  x : A ⊢ U ∋ B
    -- --------------------------- sigma
    --        ⊢ U ∋ Σ (x : A) × B
    --
    lintCheck ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    lintCheck (bind ctx x x a') b VUni
lintCheck' ctx (Sgm _ _ _) ty =
    lintError ctx "exists type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (Mul t s) (force -> VSgm _ a b) = do
    --
    -- ⊢ A ∋ t
    -- ⊢ B [z ↦ t] ∋ s
    -- ---------------------------- pair
    -- ⊢ Σ (z : A) × B ∋ pair t s
    --
    lintCheck ctx t a
    let tv = evalTerm (size ctx) (values ctx) t
    lintCheck ctx s (run ctx.size b (vann tv a))

lintCheck' ctx (Mul _ _) ty = do
    lintError ctx "pair constructor should have pair type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' _ (Fin _) (force -> VUni) = do
    --
    -- ------------------ fin
    -- ⊢ U ∋ {:a ... :z}
    --
  return ()

lintCheck' ctx (Fin _) ty =
    lintError ctx "finite set type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (Lbl l) (force -> VFin ls)
    --
    --  :l ∈ {:a ... :z}
    -- ------------------ lbl
    -- ⊢ {:a ... :z} ∋ :l
    --
    | Set.member l ls
    = return ()

    | otherwise
    = lintError ctx ("label" <+> prettyLabel l <+> "is not in the set" <+> prettyVTermCtx ctx (VFin ls)) []

lintCheck' ctx (Lbl _) ty   =
    lintError ctx "label should have a finite set type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' _   Uni         (force -> VUni) =
    --
    --
    -- --------- type in type
    --  ⊢ U ∋ U
    --
    pure ()

lintCheck' ctx Uni         ty   =
    lintError ctx "U should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (Muu t)     (force -> VUni)= do
    --
    --  ⊢ Desc ∋ d
    -- ------------ mu
    --  ⊢ U ∋ μ d
    --
    lintCheck ctx t VDsc
lintCheck' ctx (Muu _)     ty =
    lintError ctx "mu should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (Con t)     (force -> ty@(VMuu d)) = do
    --
    --  ⊢ evalDesc d (μ d) ∋ t
    -- ------------------------ con
    --  ⊢ μ d ∋ con t
    --
    lintCheck ctx t (vemb (vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, ty]))

lintCheck' ctx (Con _)     ty =
    lintError ctx "con should have type mu"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' _   Dsc         (force -> VUni) =
    --
    --
    -- ------------ dsc
    --  ⊢ U ∋ Desc
    --
    pure ()

lintCheck' ctx Dsc         ty   =
    lintError ctx "Desc should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' _   De1         (force -> VDsc) =
    --
    --
    -- ------------- dsc-1
    --  ⊢ Desc ∋ `1
    --
    pure ()
lintCheck' ctx De1         ty =
    lintError ctx "`1 should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (DeS t s)   (force -> VDsc) = do
    --
    --  ⊢ U ∋ s
    --  ⊢ s -> Desc ∋ d
    -- ----------------- dsc-Σ
    --  ⊢ Desc ∋ `S s d
    --
    lintCheck ctx t VUni
    lintCheck ctx s (VPie "_" (evalTerm ctx.size ctx.values t) (Closure EmptyEnv Dsc))

lintCheck' ctx (DeS _ _)   ty =
    lintError ctx "`S should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (DeX t)   (force -> VDsc) =
    --
    --  ⊢ Desc ∋ d
    -- ----------------- dsc-X
    --  ⊢ Desc ∋ `X d
    --
    lintCheck ctx t VDsc

lintCheck' ctx (DeX _)   ty =
    lintError ctx "`X should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintCheck' ctx (Emb e)     a    = do
    --
    --  ⊢ e ∈ B
    --    A ≡ B
    -- --------- emb
    --  ⊢ A ∋ e
    --
    b <- lintInfer ctx e
    case convTerm (mkConvCtx ctx.size ctx.names' ctx.types' ctx.nscope) VUni a b of
        Right () -> pure ()
        Left err -> lintError ctx "Couldn't match types"
            [ "expected:" <+> prettyVTermCtx ctx a
            , "actual:" <+> prettyVTermCtx ctx b
            , err
            ]

lintCheck' ctx (WkT w t) a =
    lintCheck' (weakenLintCtx w ctx) t a

lintInfer' :: forall ctx ctx'. LintCtx ctx ctx' -> Elim ctx -> Either String (VTerm ctx')
lintInfer' ctx (Var x)   =
    --
    --  (x : A) ∈ Γ
    -- ------------- var
    --   Γ ⊢ x ∈ A
    --
    return (lookupEnv x ctx.types)

lintInfer' ctx (Gbl g)   =
    -- Global is similar to variable.
    return (sinkSize ctx.size (gblType g))

lintInfer' ctx (App f t) = do
    --
    --  ⊢ f ∈ Π (x : A) → B
    --  ⊢ A ∋ t
    -- --------------------- app
    --  ⊢ f t ∈ B [x ↦ t]
    --
    fty <- lintInfer ctx f
    case force fty of
        VPie _ a b -> do
            lintCheck ctx t a
            let t' = evalTerm ctx.size ctx.values t
            return (run ctx.size b (vann t' a))
        _ -> lintError ctx "Function application head is not pi-type"
            [ "actual:" <+> prettyVTermCtx ctx fty
            ]

lintInfer' ctx (Sel e s) = do
    --
    --  ⊢ e ∈ Σ (z : A) × B
    -- --------------------- fst
    --  ⊢ e .fst ∈ A
    --
    --  ⊢ e ∈ Σ (z : A) × B
    -- ----------------------------- snd
    --  ⊢ e .snd ∈ B [ z ↦ e .fst ]
    --
    et <- lintInfer ctx e
    case force et of
        VSgm _ a b
            | s == "fst" -> return a
            | s == "snd" -> return (run (size ctx) b (evalElim ctx.size ctx.values (Sel e "fst")))
            | otherwise  -> lintError ctx ("Sigma type doesn't have field" <+> prettySelector s) []

        _ -> lintError ctx "Selector application head does not have a selectable type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintInfer' ctx (Swh e m ts) = do
    et <- lintInfer ctx e
    case force et of
        VFin ls -> do
            unless (ls == Map.keysSet ts) $ lintError ctx "Switch cases do not match"
                [ "actual:" <+> prettyVTermCtx ctx (VFin (Map.keysSet ts))
                , "expected:" <+> prettyVTermCtx ctx (VFin ls)
                ]

            -- {:ls...} -> U ∋ M
            let mt = VPie "_" et (Closure EmptyEnv Uni)
            lintCheck ctx m mt
            let mv x = vemb (vapp ctx.size (vann (evalTerm ctx.size ctx.values m) mt) x)

            ifor_ ts $ \l t -> do
                lintCheck ctx t (mv (VLbl l))

            return (mv (vemb (evalElim ctx.size ctx.values e)))

        _ -> lintError ctx "Switch case scrutinee doesn't have finite set type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintInfer' ctx (DeI e m c1 cS cX) = do
    --
    -- ⊢ e ∈ Desc
    -- ⊢ Desc → U ∋ M
    -- ⊢ M `1                                                          ∋ c1
    -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
    -- ⊢ Π (D : Desc) → M D → M (`X D)                                 ∋ cX
    ------------------------------------------------------------------------ desc-ind
    -- ⊢ indDesc e M c1 cS cX ∈ M e
    --

    -- ⊢ e ∈ Desc
    et <- lintInfer ctx e
    case force et of
        VDsc -> do
            -- ⊢ Desc → U ∋ M
            let mt = evalTerm ctx.size EmptyEnv descIndMotive
            lintCheck ctx m mt

            let mv :: VElim ctx'
                mv = vann (evalTerm ctx.size ctx.values m) mt

            -- ⊢ M `1 ∋ c1
            lintCheck ctx c1 $ evalTerm ctx.size (EmptyEnv :> mv) descIndMotive1

            -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
            lintCheck ctx cS $ evalTerm ctx.size (EmptyEnv :> mv) descIndMotiveS

            -- ⊢ Π (D : Desc) → M D → M (`X D) ∋ cX
            lintCheck ctx cX $ evalTerm ctx.size (EmptyEnv :> mv) descIndMotiveX

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e
            return $ evalTerm ctx.size (ctx.values :> mv :> ev) (var I1 @@ var IZ)

        _ -> lintError ctx "Desc induction scrutinee doesn't have type Desc"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintInfer' ctx (Ind e m t) = do
    --
    --  ⊢                                                      e ∈ μ D
    --  ⊢                                                μ D → U ∋ M
    --  ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
    -- ---------------------------------------------------------------- ind
    --  ⊢ ind e M t ∈ M e
    --

    -- ⊢ e ∈ μ D
    et <- lintInfer ctx e
    case force et of
        VMuu d -> do
            -- ⊢ μ D → U ∋ M
            let mt = VPie "_" et (Closure EmptyEnv Uni)
            lintCheck ctx m mt

            let mv :: VElim ctx'
                mv = vann (evalTerm ctx.size ctx.values m) mt

            -- ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
            lintCheck ctx t $ evalTerm ctx.size (EmptyEnv :> vann d VDsc :> mv) muMotiveT

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e
            return $ evalTerm ctx.size (ctx.values :> mv :> ev) (var I1 @@ var IZ)

        _ -> lintError ctx "ind doesn't have type mu"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintInfer' ctx (Ann t a) = do
    --
    --  ⊢ U ∋ A
    --  ⊢ A ∋ t
    -- --------------- ann
    --  ⊢ (t : A) ∈ A
    --
    lintCheck ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    lintCheck ctx t a'
    return a'

lintInfer' ctx (Let x e f) = do
    --
    --  ⊢ e ∈ A
    --  ⊢ f [x ↦ e] ∈ B
    -- ---------------------- let
    --  ⊢ let x = e in f ∈ B
    --
    a <- lintInfer ctx e
    let e' = evalElim ctx.size ctx.values e
    lintInfer (bind' ctx x e' a) f

lintInfer' ctx (WkE w e) =
    lintInfer' (weakenLintCtx w ctx) e
