-- | Elaboration.
--
-- In case of @poritt@ this is just a type-checker,
-- we don't elaborate anything.
module PoriTT.Elab (
    ElabCtx,
    emptyElabCtx,
    check,
    infer,
) where

import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Loc
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value
import PoriTT.Well

-------------------------------------------------------------------------------
-- Elaboration context
-------------------------------------------------------------------------------

-- | Elaboration context.
--
data ElabCtx ctx ctx' = ElabCtx
    { names   :: !(Env ctx Name)
    , names'  :: !(Env ctx' Name)
    , nscope  :: !NameScope
    , values  :: !(EvalEnv ctx ctx')
    , types   :: !(Env ctx (VTerm ctx'))
    , types'  :: !(Env ctx' (VTerm ctx'))
    , stages  :: Env ctx Stage
    , cstage  :: Stage
    , size    :: !(Size ctx')
    , loc     :: !(Loc)
    , doc     :: ![Doc]
    }

sinkElabCtx :: Name -> VTerm ctx' -> ElabCtx ctx ctx' -> ElabCtx ctx (S ctx')
sinkElabCtx x' t' (ElabCtx xs xs' ns v ts ts' ss cs s l pp) =
    ElabCtx xs (xs' :> x') ns (mapSink v) (mapSink ts) (mapSink ts' :> sink t') ss cs (SS s) l pp

-- | Empty elaboration context.
--
-- Needs global 'NameScope' for pretty-printing.
--
emptyElabCtx :: NameScope -> ElabCtx EmptyCtx EmptyCtx
emptyElabCtx ns = ElabCtx EmptyEnv EmptyEnv ns EmptyEnv EmptyEnv EmptyEnv EmptyEnv stage0 SZ (startLoc "<unknown>") []

bind
    :: ElabCtx ctx ctx'
    -> Name                     -- ^ term name
    -> Name                     -- ^ name in types
    -> VTerm ctx'               -- ^ type
    -> ElabCtx (S ctx) (S ctx')
bind ctx x x' a = bind' (sinkElabCtx x' a ctx) x (valZ (size ctx)) (sink a)

bind'
    :: ElabCtx ctx ctx'
    -> Name              -- ^ variable name
    -> VElim ctx'        -- ^ value
    -> VTerm ctx'        -- ^ type
    -> ElabCtx (S ctx) ctx'
bind' (ElabCtx xs xs' ns v ts ts' ss cs s l pp) x t a = ElabCtx
    { names   = xs :> x
    , names'  = xs'
    , nscope  = ns
    , values  = v :> t
    , types   = ts :> a
    , types'  = ts'
    , stages  = ss :> cs
    , cstage  = cs
    , size    = s
    , loc     = l
    , doc     = pp
    }

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

elabError :: ElabCtx ctx ctx' -> Doc -> [Doc] -> Either String a
elabError ctx msg extras = Left $ ppRender False $ ppHanging
    (prettyLoc (loc ctx) <> ":" <+> msg)
    [ "*" <+> e
    | e <- extras ++ take 5 (doc ctx)
    ]

prettyVTermCtx :: ElabCtx ctx ctx' -> VTerm ctx' -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names'

prettyNamesTypes :: Size ctx' -> NameScope -> Env ctx' Name -> Env ctx Name -> Env ctx (VTerm ctx') -> [Doc]
prettyNamesTypes _ _  _   EmptyEnv  EmptyEnv  =  []
prettyNamesTypes s ns env (xs :> x) (ts :> t) =
    (prettyName x <+> ":" <+> t') :
    prettyNamesTypes s ns env xs ts
  where
    t' = case quoteTerm UnfoldElim s t of
        Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
        Right n  -> prettyTerm ns env 0 n

-------------------------------------------------------------------------------
-- Check & Infer wrappers
-------------------------------------------------------------------------------

-- | Check term ('Term') against a type (as 'VTerm').
check
    :: ElabCtx ctx ctx'           -- ^ Elaboration context
    -> Well ctx                   -- ^ Raw term
    -> VTerm ctx'                 -- ^ Expected type
    -> Either String (Term ctx)   -- ^ Elaborated term
check ctx t a = do
    let d = "When checking that" <+> prettyWell ctx.nscope ctx.names 0 t <+> "has type" <+> prettyVTermCtx ctx a
    check' ctx { doc = d : doc ctx } t a

-- | Infer type of an elimination ('Elim').
infer
    :: ElabCtx ctx ctx'                       -- ^ Elaboration context
    -> Well ctx                               -- ^ Raw elimination
    -> Either String (Elim ctx, VTerm ctx')   -- ^ Elaborated elimination and its type
infer ctx e = do
    let d = "When infering type of" <+> prettyWell ctx.nscope ctx.names 0 e
    infer' ctx { doc = d : doc ctx } e

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

check'
    :: ElabCtx ctx ctx'           -- ^ Elaboration context
    -> Well ctx                   -- ^ Raw term
    -> VTerm ctx'                 -- ^ Expected type
    -> Either String (Term ctx)   -- ^ Elaborated term
check' ctx (WLoc l t)   a =
    check' ctx { loc = l } t a
check' ctx _            (force -> VEmb (VErr msg)) = do
    elabError ctx "Type evaluation error"
        [ ppStr (show msg)
        ]

check' ctx (WLam x t)   (force -> VPie y a b) = do
    let ctx' = bind ctx x y a
    t' <- check ctx' t (runZ ctx.size b)
    return (Lam x t')
check' ctx (WLam _ _) ty =
    elabError ctx "Lambda abstraction should have function type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WPie x a b) (force -> VUni) = do
    a' <- check ctx a VUni
    let av = evalTerm (size ctx) (values ctx) a'
    b' <- check (bind ctx x x av) b VUni
    return (Pie x a' b')
check' ctx (WPie _ _ _) ty =
    elabError ctx "forall type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WSgm x a b) (force -> VUni) = do
    a' <- check ctx a VUni
    let av = evalTerm (size ctx) (values ctx) a'
    b' <- check (bind ctx x x av) b VUni
    return (Sgm x a' b')
check' ctx (WSgm _ _ _) ty =
    elabError ctx "exists type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WMul t s) (force -> VSgm _ a b) = do
    t' <- check' ctx t a
    let tv = evalTerm (size ctx) (values ctx) t'
    s' <- check ctx s (run ctx.size b (vann tv a))
    return (Mul t' s')
check' ctx (WMul _ _) ty = do
    elabError ctx "pair constructor should have pair type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        -- , "forced:" <+> prettyVTermCtx ctx (force ty)
        ]
check' _ (WFin ls) (force -> VUni) = do
    return (Fin ls)
check' ctx (WFin _) ty =
    elabError ctx "finite set type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WLbl l ts) (force -> VFin ls)
    | not (null ts)
    = elabError ctx ("label" <+> prettyLabel l <+> "is applied to arguments but checked against finite set type") []

    | Set.member l ls
    = return (Lbl l)

    | otherwise
    = elabError ctx ("label" <+> prettyLabel l <+> "is not in the set" <+> prettyVTermCtx ctx (VFin ls)) []

check' ctx (WLbl l ts) (force -> VMuu (force -> VDeS (force -> VFin ls) d))
    | Set.notMember l ls
    = elabError ctx ("label" <+> prettyLabel l <+> "is not in the set" <+> prettyVTermCtx ctx (VFin ls)) []

    | otherwise
    = do
        let d' = vann d $ (VPie "_" (VFin ls) (Closure EmptyEnv Dsc))
        t' <- check ctx (wList ts) $ vemb $ vapps ctx.size (vgbl ctx.size evalDescGlobal)
            [ vemb (vapp ctx.size d' (VLbl l))
            , VMuu (VDeS (VFin ls) d)
            ]

        return $ Con (Mul (Lbl l) t')

check' ctx (WLbl _ _) ty =
    elabError ctx "label should have finite set type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' _   WUni         (force -> VUni) =
    pure Uni
check' ctx WUni         ty =
    elabError ctx "U should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WMuu t)     (force -> VUni)= do
    t' <- check ctx t VDsc
    return (Muu t')
check' ctx (WMuu _)     ty =
    elabError ctx "mu should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WCon t)     (force -> ty@(VMuu d))= do
    t' <- check ctx t $ vemb $ vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, ty]
    return (Con t')
check' ctx (WCon _)     ty =
    elabError ctx "con should have type mu"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

check' _   WDsc         (force -> VUni) =
    pure Dsc
check' ctx WDsc         ty =
    elabError ctx "Desc should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' _   WDe1         (force -> VDsc) =
    pure De1
check' ctx WDe1         ty =
    elabError ctx "`1 should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WDeS t s)   (force -> VDsc) = do
    t' <- check ctx t VUni
    s' <- check ctx s (VPie "_" (evalTerm ctx.size ctx.values t') (Closure EmptyEnv Dsc))
    return (DeS t' s')

check' ctx (WDeS _ _)   ty =
    elabError ctx "`S should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
check' ctx (WDeX t)   (force -> VDsc) = do
    t' <- check ctx t VDsc
    return (DeX t')
check' ctx (WDeX _)   ty =
    elabError ctx "`X should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

check' ctx (WCod t)     (force -> VUni)= do
    t' <- check ctx t VUni
    return (Cod t')
check' ctx (WCod _)     ty =
    elabError ctx "Code should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

check' ctx (WQuo t)     (force -> VCod a) = do
    t' <- check ctx { cstage = pred ctx.cstage } t a
    return (Quo t')
check' ctx (WQuo _)     ty =
    elabError ctx "quote should have type Code"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

check' ctx WHol        ty =
    elabError ctx "Checking a hole" $
        [ "type:" <+> prettyVTermCtx ctx ty
        ] ++
        (prettyNamesTypes ctx.size ctx.nscope ctx.names' ctx.names ctx.types)

check' ctx e            a = do
    (e', et) <- infer ctx e
    -- traceM $ "CONV: " ++ show (ctx.names', e, et, a)
    case convTerm (mkConvCtx ctx.size ctx.names' ctx.types' ctx.nscope) VUni a et of
        Right () -> pure (Emb e')
        Left err -> elabError ctx "Couldn't match types"
            [ "expected:" <+> prettyVTermCtx ctx a
            , "actual:" <+> prettyVTermCtx ctx et
            , err
            ]

infer' :: forall ctx ctx'. ElabCtx ctx ctx' -> Well ctx -> Either String (Elim ctx, VTerm ctx')
infer' ctx (WLoc l r)
    = infer' ctx { loc = l } r
infer' ctx (WVar i) = do
    let s = lookupEnv i ctx.stages
    when (s /= ctx.cstage) $ do
        elabError ctx "Variable used at different stage"
            [ "variable:" <+> prettyName (lookupEnv i ctx.names)
            , "expected:" <+> prettyStage ctx.cstage
            , "actual:  " <+> prettyStage s
            ]

    pure (Var i, lookupEnv i ctx.types)
infer' ctx (WGbl g) =
    pure (Gbl g, sinkSize ctx.size (gblType g))
infer' ctx WHol =
    elabError ctx
    "Cannot infer type of a hole"
    []
infer' ctx (WLam _ _) =
    elabError ctx
    "Cannot infer type of a lambda abstraction"
    []
infer' ctx (WMul _ _) =
    elabError ctx
    "Cannot infer type of a pair constructor"
    []
infer' ctx (WCon _) =
    elabError ctx
    "Cannot infer type of a con constructor"
    []
infer' ctx (WLbl _ _) =
    elabError ctx
    "Cannot infer type of a label"
    []
infer' ctx (WQuo _) =
    elabError ctx
    "Cannot infer type of a quote"
    []
infer' ctx (WPie x a b) = do
    a' <- check ctx a VUni
    let av = evalTerm (size ctx) (values ctx) a'
    b' <- check (bind ctx x x av) b VUni
    return (Ann (Pie x a' b') Uni, VUni)
infer' ctx (WSgm x a b) = do
    a' <- check ctx a VUni
    let av = evalTerm (size ctx) (values ctx) a'
    b' <- check (bind ctx x x av) b VUni
    return (Ann (Sgm x a' b') Uni, VUni)
infer' _   (WFin ls) =
    return (Ann (Fin ls) Uni, VUni)
infer' _   WUni =
    return (Ann Uni Uni, VUni)
infer' _   WDsc =
    return (Ann Dsc Uni, VUni)
infer' _   WDe1 =
    return (Ann De1 Dsc, VDsc)
infer' ctx (WDeX t) = do
    t' <- check ctx t VDsc
    return (Ann (DeX t') Dsc, VDsc)
infer' ctx (WDeS t s) = do
    t' <- check ctx t VUni
    let tv = evalTerm ctx.size ctx.values t'
    s' <- check ctx s (VPie "_" tv (Closure EmptyEnv Dsc))
    return (Ann (DeS t' s') Dsc, VDsc)
infer' ctx (WMuu t) = do
    t' <- check ctx t VDsc
    return (Ann (Muu t') Uni, VUni)
infer' ctx (WCod a) = do
    a' <- check ctx a VUni
    return (Ann (Cod a') Uni, VUni)
infer' ctx (WApp f t) = do
    (f', ft) <- infer ctx f
    case force ft of
        VPie _ a b -> do
            t' <- check ctx t a
            let tv = evalTerm (size ctx) (values ctx) t'
            return (App f' t', run (size ctx) b (vann tv a))
        _ -> elabError ctx "Function application head does not have a pi-type"
            [ "actual:" <+> prettyVTermCtx ctx ft
            ]
infer' ctx (WSel e s) = do
    (e', et) <- infer ctx e
    case force et of
        VSgm _ a b
            | s == "fst" -> return (Sel e' s, a)
            | s == "snd" -> return (Sel e' s, run (size ctx) b (evalElim ctx.size ctx.values (Sel e' "fst")))
            | otherwise  -> elabError ctx ("Sigma type doesn't have field" <+> prettySelector s) []

        -- TODO: pie with a ~ WFin
        _ -> elabError ctx "Selector application head does not have a selectable type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

infer' ctx (WSwh e m ts) = do
    (e', et) <- infer ctx e
    case force et of
        VFin ls -> do
            unless (ls == Map.keysSet ts) $ elabError ctx "Switch cases do not match"
                [ "actual:" <+> prettyVTermCtx ctx (VFin (Map.keysSet ts))
                , "expected:" <+> prettyVTermCtx ctx (VFin ls)
                ]

            -- {:ls...} -> U ∋ M
            let mt = VPie "_" et (Closure EmptyEnv Uni)
            m' <- check ctx m mt
            let mv :: VElim ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

            -- in { :l -> t }
            -- M :l ∋ t
            ts' <- ifor ts $ \l t -> do
                check ctx t $ evalTerm ctx.size (EmptyEnv :> mv) (var IZ @@  Lbl l)

            let ev = evalElim ctx.size ctx.values e'
            return (Swh e' m' ts', evalTerm ctx.size (ctx.values :> mv :> ev) (var I1 @@ var IZ))

        _ -> elabError ctx "Switch case scrutinee doesn't have finite set type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

infer' ctx (WDeI e m c1 cS cX) = do
    -- ⊢ e ∈ Desc
    (e', et) <- infer ctx e
    case force et of
        VDsc -> do
            -- ⊢ Desc → U ∋ M
            let mt = evalTerm ctx.size EmptyEnv descIndMotive
            m' <- check ctx m mt
            let mv :: VElim ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

            -- ⊢ M `1 ∋ c1
            c1' <- check ctx c1 $ evalTerm ctx.size (EmptyEnv :> mv) descIndMotive1

            -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
            cS' <- check ctx cS $ evalTerm ctx.size (EmptyEnv :> mv) descIndMotiveS

            -- ⊢ Π (D : Desc) → M D → M (`X D) ∋ cX
            cX' <- check ctx cX $ evalTerm ctx.size (EmptyEnv :> mv) descIndMotiveX

            -- ∈ M e
            let ev = evalElim ctx.size ctx.values e'
            return
              ( DeI e' m' c1' cS' cX'
              , evalTerm ctx.size (ctx.values :> mv :> ev) (var I1 @@ var IZ)
              )

        _ -> elabError ctx "Desc induction scrutinee doesn't have type Desc"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

infer' ctx (WInd e m t) = do
    -- ⊢ e ∈ μ D
    (e', et) <- infer ctx e
    case force et of
        VMuu d -> do
            -- ⊢ μ D → U ∋ M
            let mt = VPie "_" et (Closure EmptyEnv Uni)
            m' <- check ctx m mt
            let mv :: VElim ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

            -- ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
            t' <- check ctx t $ evalTerm ctx.size (EmptyEnv :> vann d VDsc :> mv) muMotiveT

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e'
            return
                ( Ind e' m' t'
                , evalTerm ctx.size (ctx.values :> mv :> ev) (var I1 @@ var IZ)
                )

        _ -> elabError ctx "ind argument doesn't have type mu"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

infer' ctx (WSpl e) = do
    (e', et) <- infer ctx { cstage = succ ctx.cstage } e
    case force et of
        VCod a -> do
            return (Spl e', a)

        _ -> elabError ctx "splice argument doesn't have type Code"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

infer' ctx (WAnn t s) = do
    s' <- check ctx s VUni
    let sv = evalTerm (size ctx) (values ctx) s'
    t' <- check ctx t sv
    return (Ann t' s', sv)
infer' ctx (WLet x t s) = do
    (t', tt) <- infer ctx t
    let tv = evalElim (size ctx) (values ctx) t'
    (s', st) <- infer (bind' ctx x tv tt) s
    return (Let x t' s', st)

wList :: [Well ctx] -> Well ctx
wList = foldr WMul (WLbl (mkLabel "tt") [])
