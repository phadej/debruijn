-- | Beta-eta conversion checking
--
-- We can check for beta-eta equality in semantic domain, i.e. on 'VTerm's and 'VElim's.
module PoriTT.Conv (
    convTerm,
    convElim,
    ConvCtx,
    mkConvCtx,
) where

import qualified Data.Map.Strict as Map

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Term
import PoriTT.Used

-- | Conversion context.
data ConvCtx ctx = ConvCtx
    { size   :: Size ctx
    , names  :: Env ctx Name
    , types  :: Env ctx (VTerm ctx)
    , nscope :: NameScope
    }

bind :: Name -> VTerm ctx -> ConvCtx ctx -> ConvCtx (S ctx)
bind x t (ConvCtx s xs ts gs) = ConvCtx (SS s) (xs :> x) (mapSink ts :> sink t) gs

-- | Create conversion context.
--
-- Requires
--
-- * context size
--
-- * names of the variables in the cotnext (for pretty printing)
--
-- * types of things in context
--
-- * and a global 'NameScope' (for pretty-printing)
--
mkConvCtx :: Size ctx -> Env ctx Name -> Env ctx (VTerm ctx) -> NameScope -> ConvCtx ctx
mkConvCtx = ConvCtx

prettyVTermCtx :: ConvCtx ctx -> VTerm ctx -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names

lookupLvl :: ConvCtx ctx -> Lvl ctx -> Name
lookupLvl ctx l = lookupEnv (lvlToIdx ctx.size l) ctx.names

mismatch :: Doc -> Doc -> Doc -> Either Doc a
mismatch t x y = Left $ t <+> "mismatch:" <+> x <+> "/=" <+> y

notConvertible :: ConvCtx ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Either Doc ()
notConvertible ctx ty x y = Left $ ppSep
    [ "not convertible:"
    , prettyVTermCtx ctx ty <+> "|-"
    , prettyVTermCtx ctx x <+> "/="
    , prettyVTermCtx ctx y
    ]

notType :: ConvCtx ctx -> VTerm ctx -> Either Doc ()
notType ctx ty = Left $ ppSep
    [ "CONV PANIC: NOT A TYPE"
    , prettyVTermCtx ctx ty
    ]

-- | Beta-eta conversion checking of terms.
--
-- The last argument is a common type of the terms.
-- The conversion checking is (somewhat) type-directed, we need
-- types for do eta-expansion.
--
convTerm :: ConvCtx ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Either Doc ()
convTerm ctx ty x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convTerm' ctx ty x y

-- | Beta-eta conversion checking of eliminations.
convElim :: ConvCtx ctx -> VElim ctx -> VElim ctx -> Either Doc ()
convElim ctx x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convElim' ctx x y

-------------------------------------------------------------------------------
-- Workers
-------------------------------------------------------------------------------

convTerm' :: ConvCtx ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Either Doc ()
convTerm' ctx (VEmb (VGbl _ _ t)) x y  = convTerm ctx (vemb t) x y
convTerm' ctx ty (VEmb (VGbl _ _ x)) y = convTerm ctx ty (vemb x) y
convTerm' ctx ty x (VEmb (VGbl _ _ y)) = convTerm ctx ty x (vemb y)

convTerm' ctx (VEmb (VAnn t _)) x y = convTerm' ctx t x y

-- ⊢ U ∋ t ≡ s
convTerm' _   VUni VUni           VUni           = pure ()
convTerm' _   VUni VDsc           VDsc           = pure ()
convTerm' ctx VUni (VPie x a1 b1) (VPie _ a2 b2) = convTerm ctx VUni a1 a2 >> convTerm (bind x a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
convTerm' ctx VUni (VSgm x a1 b1) (VSgm _ a2 b2) = convTerm ctx VUni a1 a2 >> convTerm (bind x a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
convTerm' ctx VUni (VMuu x)       (VMuu y)       = convTerm ctx VDsc x y
convTerm' ctx VUni (VEmb (VNeu x sp1)) (VEmb (VNeu y sp2))   = convNeutral ctx x sp1 y sp2
convTerm' _   VUni (VFin ls1)     (VFin ls2)     = if ls1 == ls2 then pure () else mismatch "finite set" (prettyLabels ls1) (prettyLabels ls2)
convTerm' ctx VUni (VCod x)       (VCod y)       = convTerm ctx VUni x y
convTerm' ctx VUni x              y              = notConvertible ctx VUni x y

-- ⊢ Π (x : A) → B ∋ t ≡ s
convTerm' ctx (VPie _ a b) (VLam x b1)    (VLam _ b2)    = convTerm (bind x a ctx) (runZ ctx.size b) (runZ ctx.size b1)  (runZ ctx.size b2)
convTerm' ctx (VPie _ a b) (VLam x b1)    (VEmb u)       = convTerm (bind x a ctx) (runZ ctx.size b) (runZ ctx.size b1)  (etaLam ctx.size u)
convTerm' ctx (VPie _ a b) (VEmb t)       (VLam x b2)    = convTerm (bind x a ctx) (runZ ctx.size b) (etaLam ctx.size t) (runZ ctx.size b2)
convTerm' ctx (VPie x a b) (VEmb t)       (VEmb u)       = convTerm (bind x a ctx) (runZ ctx.size b) (etaLam ctx.size t) (etaLam ctx.size u)
-- convTerm' ctx (VPie _ _ _) (VNeu x sp1)   (VNeu y sp2)   = convNeutral ctx x sp1 y sp2
convTerm' ctx (VPie z a b) x              y              = notConvertible ctx (VPie z a b) x y

-- ⊢ Σ (z : A) × B ∋ t ≡ s
convTerm' ctx (VSgm _ a b) (VMul x1 y1)   (VMul x2 y2)   = convTerm ctx a x1 x2 >> convTerm ctx (run ctx.size b (vann x1 a)) y1 y2
convTerm' ctx (VSgm _ a b) (VMul x y)     (VEmb q)       = convTerm ctx a x (vemb (vsel ctx.size q "fst")) >> convTerm ctx (run ctx.size b (vann x a)) y (vemb (vsel ctx.size q "snd"))
convTerm' ctx (VSgm _ a b) (VEmb p)       (VMul x y)     = convTerm ctx a (vemb (vsel ctx.size p "fst")) x >> convTerm ctx (run ctx.size b (vann x a)) (vemb (vsel ctx.size p "snd")) y
convTerm' ctx (VSgm _ a b) (VEmb p)       (VEmb q)       = do
    let p1 = vsel ctx.size p "fst"
    convTerm ctx a                   (vemb p1)                      (vemb (vsel ctx.size q "fst"))
    convTerm ctx (run ctx.size b p1) (vemb (vsel ctx.size p "snd")) (vemb (vsel ctx.size q "snd"))
-- convTerm' ctx (VSgm _ _ _) (VNeu x sp1)   (VNeu y sp2)   = convNeutral ctx x sp1 y sp2
convTerm' ctx (VSgm z a b) x              y              = notConvertible ctx (VSgm z a b) x y

-- ⊢ {:a ... :z} ∋ t ≡ s
convTerm' _   (VFin _)  (VLbl l1)    (VLbl l2)    = if l1 == l2 then pure () else mismatch "label" (prettyLabel l1) (prettyLabel l2)
convTerm' _   (VFin ls) _            _
    -- eta expansion singletons: treat all elements equally
    | length ls == 1                              = pure ()
convTerm' ctx (VFin _)  (VEmb x)     (VEmb y)     = convElim ctx x y
convTerm' ctx (VFin ls) x            y            = notConvertible ctx (VFin ls) x y

-- ⊢ Desc ∋ t ≡ s
convTerm' _   VDsc VDe1           VDe1           = pure ()
convTerm' ctx VDsc (VDeS t1 s1)   (VDeS t2 s2)   = do
    convTerm ctx VUni t1 t2
    convTerm ctx (VPie "S" t1 (Closure EmptyEnv Dsc)) s1 s2
convTerm' ctx VDsc (VDeX t1)      (VDeX t2)      = do
    convTerm ctx VDsc t1 t2
convTerm' ctx VDsc (VEmb x)       (VEmb y)       = convElim ctx x y
convTerm' ctx VDsc x              y              = notConvertible ctx VDsc x y

-- ⊢ μ d ∋ t ≡ s
convTerm' ctx (VMuu d) (VCon x)       (VCon y)     = do
    let xty = vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, VMuu d]
    convTerm ctx (vemb xty) x y
convTerm' ctx (VMuu _) (VEmb x)       (VEmb y)     = convElim ctx x y
convTerm' ctx (VMuu d) x              y            = notConvertible ctx (VMuu d) x y

-- ⊢ Code a ∋ t ≡ s
convTerm' ctx (VCod a) (VQuo x)       (VQuo y)     = do
    convTerm ctx a x y
convTerm' ctx (VCod _) (VEmb x)       (VEmb y)     = convElim ctx x y
convTerm' ctx (VCod a) x              y            = notConvertible ctx (VCod a) x y

-- Only neutral terms can be convertible under neutral type
convTerm' ctx (VEmb VNeu {})     (VEmb x) (VEmb y) = convElim ctx x y
convTerm' ctx (VEmb (VNeu h sp)) x y = notConvertible ctx (VEmb (VNeu h sp)) x y

convTerm' _   (VEmb (VErr msg)) _ _ = Left $ ppText $ show msg

-- value constructors cannot be types
convTerm' ctx ty@VLam {} _ _ = notType ctx ty
convTerm' ctx ty@VDe1 {} _ _ = notType ctx ty
convTerm' ctx ty@VDeS {} _ _ = notType ctx ty
convTerm' ctx ty@VDeX {} _ _ = notType ctx ty
convTerm' ctx ty@VCon {} _ _ = notType ctx ty
convTerm' ctx ty@VMul {} _ _ = notType ctx ty
convTerm' ctx ty@VLbl {} _ _ = notType ctx ty
convTerm' ctx ty@VQuo {} _ _ = notType ctx ty

convElim' :: ConvCtx ctx -> VElim ctx -> VElim ctx -> Either Doc ()
-- Globals
convElim' _  (VGbl g1 VNil _) (VGbl g2 VNil _)
    | gblName g1 == gblName g2   = pure ()
-- otherwise we check the values
convElim' ctx (VGbl _ _ t)   u             = convElim ctx t u
convElim' ctx t              (VGbl _ _ u)  = convElim ctx t u
convElim' ctx (VNeu h1 sp1)  (VNeu h2 sp2) = convNeutral ctx h1 sp1 h2 sp2
convElim' ctx (VAnn t ty)    e             = convTerm ctx ty t (vemb e)
convElim' ctx e              (VAnn t ty)   = convTerm ctx ty (vemb e) t
convElim' _   (VErr msg)     _             = Left $ ppText $ show msg
convElim' _   _              (VErr msg)    = Left $ ppText $ show msg

-- Eta expand value of function type.
etaLam :: Size ctx -> VElim ctx -> VTerm (S ctx)
etaLam s f = vemb (vapp (SS s) (sink f) (vemb (valZ s)))

convNeutral :: ConvCtx ctx -> Lvl ctx -> Spine ctx -> Lvl ctx -> Spine ctx -> Either Doc ()
convNeutral ctx x sp1 y sp2
    | x == y    = do
        -- traceM "convNeutral"
        -- traceM $ show $ prettyVTermCtx ctx (VNeu x sp1)
        -- traceM $ show $ prettyVTermCtx ctx (VNeu y sp2)
        -- traceM $ show $ prettyVTermCtx ctx headTy
        convSpine ctx x sp1 sp2
    | otherwise = mismatch "spine head" (prettyName (lookupLvl ctx x)) (prettyName (lookupLvl ctx y))

convThese :: ConvCtx ctx -> VElim ctx -> Label -> These (VTerm ctx) (VTerm ctx) -> Either Doc ()
convThese _   _ l (This _)    = Left ("case in left:" <+> prettyLabel l)
convThese _   _ l (That _)    = Left ("case in right:" <+> prettyLabel l)
convThese ctx m l (These x y) = convTerm ctx (evalTerm ctx.size (EmptyEnv :> m) (var IZ @@ Lbl l)) x y

convSpine :: forall ctx. ConvCtx ctx -> Lvl ctx -> Spine ctx -> Spine ctx -> Either Doc ()
convSpine ctx headLvl sp1' sp2' = do
    bwd [] sp1' sp2'
  where
    headTy = lookupEnv (lvlToIdx ctx.size headLvl) ctx.types

    bwd :: [(SpinePart ctx, SpinePart ctx)] -> Spine ctx -> Spine ctx -> Either Doc ()
    bwd acc sp1 sp2 = case (unsnocSpine sp1, unsnocSpine sp2) of
        (Nothing, Nothing)           -> void $ foldParts fwd (VNeu headLvl VNil, headTy) acc
        (Just (xs, x), Just (ys, y)) -> bwd ((x,y) : acc) xs ys
        _                            -> mismatch "spine length" (ppInt (spineLength sp1')) (ppInt (spineLength sp2'))

    fwd :: (VElim ctx, VTerm ctx) -> SpinePart ctx -> SpinePart ctx -> Either Doc (VElim ctx, VTerm ctx)
    fwd (sp, (VEmb (VGbl _ _ t))) x           y =
        fwd (sp, vemb t) x y

    fwd (sp, VPie _ a b) (PApp x)    (PApp y) = do
        convTerm ctx a x y
        return (vapp ctx.size sp x, run ctx.size b (vann x a))

    fwd (sp, VSgm _ a b) (PSel x)    (PSel y)
        | x == y = case x of
            "fst" -> return (vsel ctx.size sp x, a)
            "snd" -> return (vsel ctx.size sp x, run ctx.size b (vsel ctx.size sp "fst"))
            _     -> Left $ "conv panic: sigma with" <+> prettySelector x
        | otherwise                            = mismatch "selector" (prettySelector x) (prettySelector y)

    fwd (sp, VFin ls)    (PSwh m1 xs) (PSwh m2 ys)
        | xs' /= ys'                           = mismatch "switch case labels" (prettyLabels xs') (prettyLabels ys')
        | otherwise                            = do
            convTerm ctx (VPie "_" (VFin ls) (Closure EmptyEnv Uni)) m1 m2
            let m :: VElim ctx
                m = vann m1 $ varr (VFin ls) Uni
            sequence_ (ialignWith (convThese ctx m) xs ys)
            return (vswh ctx.size sp m1 xs, vemb (vapp ctx.size m (vemb sp)))
      where
        xs' = Map.keysSet xs
        ys' = Map.keysSet ys

    fwd (sp, VDsc)   (PDeI m1 t1 s1 r1)
                     (PDeI m2 t2 s2 r2)        = do
        convTerm ctx (evalTerm ctx.size EmptyEnv         descIndMotive)  m1 m2
        let m :: VElim ctx
            m = vann m1 $ varr VDsc Uni
        convTerm ctx (evalTerm ctx.size (EmptyEnv :> m) descIndMotive1) t1 t2
        convTerm ctx (evalTerm ctx.size (EmptyEnv :> m) descIndMotiveS) s1 s2
        convTerm ctx (evalTerm ctx.size (EmptyEnv :> m) descIndMotiveX) r1 r2
        return (vdei ctx.size sp m1 t1 s1 r1, vemb (vapp ctx.size m (vemb sp)))

    fwd (sp, VMuu d)     (PInd m1 c1) (PInd m2 c2) = do
        convTerm ctx (VPie "_" (VMuu d) (Closure EmptyEnv Uni))      m1 m2
        let m :: VElim ctx
            m = vann m1 $ varr (VMuu d) Uni

            d' :: VElim ctx
            d' = vann d VDsc

        convTerm ctx (evalTerm ctx.size (EmptyEnv :> d' :> m) muMotiveT) c1 c2
        return (vind ctx.size sp m1 c1, vemb (vapp ctx.size m (vemb sp)))

    fwd (_sp, ty)        x            y            =
        Left $ "eliminator mismatch" <+> prettyVTermCtx ctx ty <+> "|-" <+> prettySpinePart ctx x <+> "/=" <+> prettySpinePart ctx y

foldParts :: Monad m => (a -> b -> b -> m a) -> a -> [(b,b)] -> m a
foldParts _ a []         = return a
foldParts f a ((x,y):zs) = f a x y >>= \b -> foldParts f b zs

unsnocSpine :: Spine ctx -> Maybe (Spine ctx, SpinePart ctx)
unsnocSpine VNil                 = Nothing
unsnocSpine (VApp sp x)          = Just (sp, PApp x)
unsnocSpine (VSel sp x)          = Just (sp, PSel x)
unsnocSpine (VSwh sp m ts)       = Just (sp, PSwh m ts)
unsnocSpine (VDeI sp m c1 c2 c3) = Just (sp, PDeI m c1 c2 c3)
unsnocSpine (VInd sp m c)        = Just (sp, PInd m c)
unsnocSpine (VSpl sp)            = Just (sp, PSpl)
{-
snocSpine :: Spine ctx -> SpinePart ctx -> Spine ctx
snocSpine sp (SApp x)          = VApp sp x
snocSpine sp (SSel s)          = VSel sp s
snocSpine sp (SSwh m ts)       = VSwh sp m ts
snocSpine sp (SDeI m c1 c2 c3) = VDeI sp m c1 c2 c3
snocSpine sp (SInd m t)        = VInd sp m t
-}

spineLength :: Spine ctx -> Int
spineLength = go 0 where
    go !n VNil              = n
    go !n (VApp sp _)       = go (n + 1) sp
    go !n (VSel sp _)       = go (n + 1) sp
    go !n (VSwh sp _ _)     = go (n + 1) sp
    go !n (VDeI sp _ _ _ _) = go (n + 1) sp
    go !n (VInd sp _ _)     = go (n + 1) sp
    go !n (VSpl sp)         = go (n + 1) sp

-- /Verterbrae/
data SpinePart ctx
    = PApp (VTerm ctx)
    | PSel !Selector
    | PSwh (VTerm ctx) (Map Label (VTerm ctx))
    | PDeI (VTerm ctx) (VTerm ctx) (VTerm ctx) (VTerm ctx)
    | PInd (VTerm ctx) (VTerm ctx)
    | PSpl
  deriving Show

prettySpinePart :: ConvCtx ctx -> SpinePart ctx -> Doc
prettySpinePart ctx (PApp v)       = "application" <+> prettyVTermCtx ctx v
prettySpinePart _   (PSel s)       = "selector" <+> prettySelector s
prettySpinePart _   (PSwh _ _)     = "switch"
prettySpinePart _   (PDeI _ _ _ _) = "indDesc"
prettySpinePart _   (PInd _ _)     = "ind"
prettySpinePart _   PSpl           = "splice"
