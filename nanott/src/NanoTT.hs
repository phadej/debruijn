-- | NanoTT is one module implementation of most things happening.
module NanoTT where

import NanoTT.Base

-------------------------------------------------------------------------------
-- * Stage
-------------------------------------------------------------------------------

newtype Stage = Stage Int
  deriving (Eq, Show)

instance Enum Stage where
    succ (Stage s) = Stage (s + 1)
    pred (Stage s) = Stage (s - 1)

    toEnum = coerce
    fromEnum = coerce

stage0 :: Stage
stage0 = Stage 0

-------------------------------------------------------------------------------
-- * Term & Elim
-------------------------------------------------------------------------------

-- | Terms @t, s, A, B@; their types are checked.
type Term :: Ctx -> Type
data Term ctx where
    Pie :: Term ctx -> Term (S ctx) -> Term ctx          -- ^ function type: @Π (x : A) → B@
    Lam :: Term (S ctx) -> Term ctx                      -- ^ lambda: @λ x → t@
    Uni :: Term ctx                                      -- ^ universe: @U@
    Cod :: Term ctx -> Term ctx                          -- ^ code: @Code A@
    Quo :: Term ctx -> Term ctx                          -- ^ quotation: @[| t |]@
    Emb :: Elim ctx -> Term ctx                          -- ^ embedded term: @e@
    Equ :: Term ctx -> Term ctx -> Term ctx -> Term ctx  -- ^ identity type: @Id A t s@
    Rfl :: Term ctx                                      -- ^ reflexivity: @refl@
    One :: Term ctx                                      -- ^ unit: @Unit@
    Ast :: Term ctx                                      -- ^ unit value: @*@

-- | Eliminations; @e, f@; their types are synthesized.
type Elim :: Ctx -> Type
data Elim ctx where
   Var :: Idx ctx -> Elim ctx                            -- ^ variable: @x@
   App :: Elim ctx -> Term ctx -> Elim ctx               -- ^ application: @f t@
   Spl :: Elim ctx -> Elim ctx                           -- ^ splice: @~ e@
   Ann :: Term ctx -> Term ctx -> Elim ctx               -- ^ annotated term: @t : A@
   Let :: Elim ctx -> Elim (S ctx) -> Elim ctx           -- ^ let expression: @let x = e in e'@

deriving instance Show (Term ctx)
deriving instance Show (Elim ctx)

-------------------------------------------------------------------------------
-- * Closures and evaluation environment
-------------------------------------------------------------------------------

-- | Evaluation environment value: A 'VElim' and a 'Lvl'.
data BElim ctx = BElim (VElim ctx) (Maybe (Lvl ctx))
  deriving Show

-- | Evaluation environment.
type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (BElim ctx')

-- | Closure, a term to be evaluated, but which needs an extra value.
type Closure :: Ctx -> Type
data Closure ctx' where Closure :: EvalEnv ctx ctx' -> Term (S ctx) -> Closure ctx'

deriving instance Show (Closure ctx)

run :: Size ctx -> Closure ctx -> BElim ctx -> VTerm ctx
run s (Closure env f) t = evalTerm s (env :> t) f

runZ :: Size ctx -> Closure ctx -> VTerm (S ctx)
runZ s clos = run (SS s) (sink clos) (bvalZ s)

valZ :: Size ctx -> VElim (S ctx)
valZ s = VNeu (lvlZ s) VNil

bvalZ :: Size ctx -> BElim (S ctx)
bvalZ s = BElim (VNeu (lvlZ s) VNil) (Just (lvlZ s))

instance Sinkable BElim where mapLvl f (BElim v l) = BElim (mapLvl f v) (fmap (mapLvl f) l)
instance Sinkable Closure where mapLvl f (Closure env t) = Closure (fmap (mapLvl f) env) t

-------------------------------------------------------------------------------
-- * Values
-------------------------------------------------------------------------------

type VTerm :: Ctx -> Type
data VTerm ctx where
    VPie :: VTerm ctx -> Closure ctx -> VTerm ctx
    VLam :: Closure ctx -> VTerm ctx
    VUni :: VTerm ctx
    VCod :: VTerm ctx -> VTerm ctx
    VQuo :: VTerm ctx -> STerm ctx -> VTerm ctx
    VEmb :: VElim ctx -> VTerm ctx  -- ^ no VAnn

    VEqu :: VTerm ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx
    VRfl :: VTerm ctx
    VOne :: VTerm ctx
    VAst :: VTerm ctx

type VElim :: Ctx -> Type
data VElim ctx where
    VErr :: String -> VElim ctx
    VAnn :: VTerm ctx -> VTerm ctx -> VElim ctx
    VNeu :: Lvl ctx -> Spine ctx -> VElim ctx

type Spine :: Ctx -> Type
data Spine ctx
    = VNil
    | VApp !(Spine ctx) (VTerm ctx)
    | VSpl !(Spine ctx)

type STerm :: Ctx -> Type
data STerm ctx where
    SUni :: STerm ctx
    -- SPie
    -- SLam
    -- SCod
    -- SQuo
    -- SEqu
    SRfl :: STerm ctx
    SOne :: STerm ctx
    SAst :: STerm ctx
    SEmb :: SElim ctx -> STerm ctx

type SElim :: Ctx -> Type
data SElim ctx where
    SErr :: String -> SElim ctx
    SVar :: Lvl ctx -> SElim ctx
    SApp :: SElim ctx -> STerm ctx -> SElim ctx
    SSpl :: VElim ctx -> SElim ctx -> SElim ctx
    SAnn :: STerm ctx -> STerm ctx -> SElim ctx
    SLet :: SElim ctx -> Closure ctx -> SElim ctx

deriving instance Show (VTerm ctx)
deriving instance Show (VElim ctx)
deriving instance Show (Spine ctx)
deriving instance Show (STerm ctx)
deriving instance Show (SElim ctx)

instance Sinkable VTerm where
    mapLvl _ VUni         = VUni
    mapLvl _ VRfl         = VRfl
    mapLvl _ VAst         = VAst
    mapLvl f (VEqu a t s) = VEqu (mapLvl f a) (mapLvl f t) (mapLvl f s)
    mapLvl f (VLam clos)  = VLam (mapLvl f clos)
    mapLvl f (VCod a)     = VCod (mapLvl f a)
    mapLvl f (VQuo t t')  = VQuo (mapLvl f t) (mapLvl f t')
    mapLvl _ VOne         = VOne
    mapLvl f (VEmb e)     = VEmb (mapLvl f e)
    mapLvl f (VPie a b)   = VPie (mapLvl f a) (mapLvl f b)

instance Sinkable VElim where
    mapLvl _ (VErr err)  = VErr err
    mapLvl f (VNeu l sp) = VNeu (mapLvl f l) (mapLvl f sp)
    mapLvl f (VAnn t s)  = VAnn (mapLvl f t) (mapLvl f s)

instance Sinkable Spine where
    mapLvl _ VNil        = VNil
    mapLvl f (VApp xs x) = VApp (mapLvl f xs) (mapLvl f x)
    mapLvl f (VSpl xs)   = VSpl (mapLvl f xs)

instance Sinkable STerm where
    mapLvl _ SUni     = SUni
    mapLvl _ SOne     = SOne
    mapLvl _ SAst     = SAst
    mapLvl _ SRfl     = SRfl
    mapLvl f (SEmb e) = SEmb (mapLvl f e)

instance Sinkable SElim where
    mapLvl _ (SErr err)  = SErr err
    mapLvl f (SVar x)    = SVar (mapLvl f x)
    mapLvl f (SApp g t)  = SApp (mapLvl f g) (mapLvl f t)
    mapLvl f (SLet a b)  = SLet (mapLvl f a) (mapLvl f b)
    mapLvl f (SAnn t s)  = SAnn (mapLvl f t) (mapLvl f s)
    mapLvl f (SSpl e e') = SSpl (mapLvl f e) (mapLvl f e')

-------------------------------------------------------------------------------
-- * Evaluation
-------------------------------------------------------------------------------

evalTerm :: Size ctx' -> EvalEnv ctx ctx' -> Term ctx -> VTerm ctx'
evalTerm s env (Pie a b)   = VPie (evalTerm s env a) (Closure env b)
evalTerm _ env (Lam t)     = VLam (Closure env t)
evalTerm _ _   Uni         = VUni
evalTerm s env (Emb e)     = vemb (evalElim s env e)
evalTerm s env (Equ a x y) = VEqu (evalTerm s env a) (evalTerm s env x) (evalTerm s env y)
evalTerm _ _   Rfl         = VRfl
evalTerm _ _   One         = VOne
evalTerm _ _   Ast         = VAst
evalTerm s env (Cod t)     = VCod (evalTerm s env t)
evalTerm s env (Quo t)     = VQuo (evalTerm s env t) (stageTerm s env t)

evalElim :: Size ctx' -> EvalEnv ctx ctx' -> Elim ctx -> VElim ctx'
evalElim _ env (Var x)   = case lookupEnv x env of BElim e _ -> e
evalElim s env (Ann t a) = vann (evalTerm s env t) (evalTerm s env a)
evalElim s env (Let t r) = evalElim s (env :> BElim (evalElim s env t) Nothing) r
evalElim s env (App f t) = vapp s (evalElim s env f) (evalTerm s env t)
evalElim s env (Spl t)   = vspl s (evalElim s env t)

-------------------------------------------------------------------------------
-- * Staging
-------------------------------------------------------------------------------

stageTerm :: Size ctx' -> EvalEnv ctx ctx' -> Term ctx -> STerm ctx'
stageTerm _ _ Uni = SUni
stageTerm _ _ _ = error "stageTerm"

stageElim :: Size ctx' -> EvalEnv ctx ctx' -> Elim ctx -> SElim ctx'
stageElim _ env (Var x) = case lookupEnv x env of
    BElim _ Nothing  -> SErr "skolem"
    BElim _ (Just l) -> SVar l
stageElim _ _ _ = error "stageElim"

-------------------------------------------------------------------------------
-- * Reductions
-------------------------------------------------------------------------------

vemb :: VElim ctx -> VTerm ctx
vemb (VAnn t _) = t
vemb e          = VEmb e

-- this reduction is not confluent, but we make more progress using
-- it -- and equate more things.
vann :: VTerm ctx -> VTerm ctx -> VElim ctx
vann (VEmb e) _ = e
vann t        s = VAnn t s

vapp :: Size ctx -> VElim ctx -> VTerm ctx -> VElim ctx
vapp s (VAnn (VLam closT) (VPie a closB)) r =
    let r' = vann r a
        rb = BElim r' Nothing
    in vann (run s closT rb) (run s closB rb)
vapp s (VAnn (VEmb e) _)                  r = vapp s e r
vapp _ (VAnn (VLam _) ty)                 _ = VErr $ "lambda annotated with " ++ show ty
vapp _ (VAnn f _)                         _ = VErr $ "applying not lambda " ++ show f
vapp _ (VNeu h sp)                        r = VNeu h (VApp sp r)
vapp _ (VErr msg)                         _ = VErr msg

vspl :: Size ctx -> VElim ctx -> VElim ctx
vspl s (VAnn (VQuo t _) (VCod a)) = vann t (vsplCodArg s a)
vspl _ (VAnn (VQuo _ _) ty)       = VErr $ "Quote annotated with not-Code: " ++ show ty
vspl s (VAnn (VEmb e)   _)        = vspl s e
vspl _ (VAnn t _)                 = VErr $ "Splicing not code " ++ show t
vspl _ (VNeu h sp)                = VNeu h (VSpl sp)
vspl _ (VErr err)                 = VErr err

-- | @Code [| U |]@
vcodUni :: VTerm ctx
vcodUni = VCod (VQuo VUni SUni)

-- | Splice @Code@ argument: @~ (a : Code [| U |])@.
vsplCodArg :: Size ctx -> VTerm ctx -> VTerm ctx
vsplCodArg s a = vemb (vspl s (vann a vcodUni))

------------------------------------------------------------------------------
-- * Quoting (reflecting values back to terms)
-------------------------------------------------------------------------------

quoteElim :: Size ctx -> VElim ctx -> Either String (Elim ctx)
quoteElim _ (VErr msg)  = Left msg
quoteElim s (VAnn t a)  = Ann <$> quoteTerm s t <*> quoteTerm s a
quoteElim s (VNeu l sp) = quoteSpine s (pure (Var (lvlToIdx s l))) sp

quoteTerm :: Size ctx -> VTerm ctx -> Either String (Term ctx)
quoteTerm _ VUni         = pure Uni
quoteTerm s (VEmb e)     = Emb <$> quoteElim s e
quoteTerm s (VPie a b)   = Pie <$> quoteTerm s a <*> quoteTerm (SS s) (runZ s b)
quoteTerm s (VLam t)     = Lam <$> quoteTerm (SS s) (runZ s t)
quoteTerm s (VEqu a x y) = Equ <$> quoteTerm s a <*> quoteTerm s x <*> quoteTerm s y
quoteTerm _ VRfl         = pure Rfl
quoteTerm _ VOne         = pure One
quoteTerm _ VAst         = pure Ast
quoteTerm s (VCod t)     = Cod <$> quoteTerm s t
quoteTerm s (VQuo _ t)   = Quo <$> quoteSTerm NZ s t

quoteSpine :: Size ctx -> Either String (Elim ctx) -> Spine ctx -> Either String (Elim ctx)
quoteSpine _ h VNil        = h
quoteSpine s h (VApp sp e) = App <$> quoteSpine s h sp <*> quoteTerm s e
quoteSpine s h (VSpl sp)   = Spl <$> quoteSpine s h sp

quoteSTerm :: Natural -> Size ctx -> STerm ctx -> Either String (Term ctx)
quoteSTerm _ _ SUni = return Uni
quoteSTerm _ _ t = error $ "quoteSTerm " ++ show t

quoteSElim :: Natural -> Size ctx -> SElim ctx -> Either String (Elim ctx)
quoteSElim _ s (SVar l) = pure (Var (lvlToIdx s l))
quoteSElim _ _ e = error $ "quoteSElim " ++ show e

-------------------------------------------------------------------------------
-- * Conversion checking
-------------------------------------------------------------------------------

-- | Conversion environment.
data ConvEnv ctx = ConvEnv
    { size   :: Size ctx
    , types  :: Env ctx (VTerm ctx)
    }
  deriving Show

-- | Extend conversion environment.
convBind :: VTerm ctx -> ConvEnv ctx -> ConvEnv (S ctx)
convBind t (ConvEnv s ts) = ConvEnv (SS s) (mapSink ts :> sink t)

-- | Typed conversion check.
--
-- @convTerm s Γ x y t@ checks @Γ ⊢ A ∋ x ≡ y@
convTerm :: ConvEnv ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Bool
convTerm ctx ty x y  =
    -- traceShow ("CONV" :: String,ctx,ty,x,y) $
    convTerm' ctx ty x y

-- | Typed conversion check, terms.
convTerm' :: ConvEnv ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Bool
--
-- -------------
--  ⊢ U ∋ U ≡ U
--
-- -------------------
--  ⊢ U ∋ Unit ≡ Unit
--
--  ⊢ U ∋ A ≡ B
--  ⊢ A ∋ t ≡ u
--  ⊢ A ∋ s ≡ v
-- -------------------------
--  ⊢ U ∋ Id A t s ≡ Id B u v
--
--  ⊢ Code [| U |] ∋ A ≡ B
-- ------------------------
--  ⊢ U ∋ Code A ≡ Code B
--
--        ⊢ U ∋ A ≡ C
--  x : A ⊢ U ∋ B ≡ D
-- -----------------------------------------------
--        ⊢ U ∋ (Π (x : A) → B) ≡ (Π (x : C) → D)
--
convTerm' _   VUni         VUni            VUni            = True
convTerm' _   VUni         VOne            VOne            = True
convTerm' ctx VUni         (VEqu a1 x1 y1) (VEqu a2 x2 y2) = convTerm ctx a1 a2 VUni && convTerm ctx a1 x1 x2 && convTerm ctx a1 y1 y2
convTerm' ctx VUni         (VCod x)        (VCod y)        = convTerm ctx vcodUni x y
convTerm' ctx VUni         (VPie a1 b1)    (VPie a2 b2)    = convTerm ctx VUni a1 a2 && convTerm (convBind a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
convTerm' ctx VUni         (VEmb x)        (VEmb y)        = convElim ctx x y
convTerm' _   VUni         _               _               = False

-- ⊢ 1        ∋ t ≡ s
-- ⊢ Id A x y ∋ t ≡ s
convTerm' _   VOne         _               _               = True
convTerm' _   (VEqu _ _ _) _               _               = True

--
--- ⊢ ~ (A : Code [| U |]) ∋ t ≡^0 s
-- ------------------------------------
--  ⊢ Code A ∋ [| t |] ≡ [| s |]
convTerm' ctx (VCod a)     (VQuo _ x)      (VQuo _ y)      = convSTerm ctx (vsplCodArg ctx.size a) x y
convTerm' ctx (VCod _)     (VEmb x)        (VEmb y)        = convElim ctx x y
convTerm' _   (VCod _)     _               _               = False

--  x : A ⊢ B ∋ t ≡ s
-- -------------------------------------------------
--        ⊢ (Π (x : A) → B) ∋ (λ x → t) ≡ (λ x → s)
--
--  x : A ⊢ B ∋ t ≡ f x
-- -------------------------------------------------
--        ⊢ (Π (x : A) → B) ∋ (λ x → t) ≡ f
--
convTerm' ctx (VPie a b)   (VLam x)        (VLam y)        = convTerm (convBind a ctx) (runZ ctx.size b) (runZ ctx.size x)   (runZ ctx.size y)
convTerm' ctx (VPie a b)   (VLam x)        (VEmb y)        = convTerm (convBind a ctx) (runZ ctx.size b) (runZ ctx.size x)   (etaLam ctx.size y)
convTerm' ctx (VPie a b)   (VEmb x)        (VLam y)        = convTerm (convBind a ctx) (runZ ctx.size b) (etaLam ctx.size x) (runZ ctx.size y)
convTerm' ctx (VPie _ _)   (VEmb x)        (VEmb y)        = convElim ctx x y
convTerm' _   (VPie _ _)   _               _               = False

convTerm' _   (VLam _)     _               _               = False
convTerm' _   (VQuo _ _)   _               _               = False
convTerm' _   VAst         _               _               = False
convTerm' _   VRfl         _               _               = False

convTerm' ctx (VEmb (VAnn t _)) x y = convTerm' ctx t x y
convTerm' _   (VEmb (VErr _))   _ _ = False

-- Only neutral terms can be convertible under neutral type
convTerm' ctx (VEmb (VNeu _ _)) (VEmb x) (VEmb y) = convElim ctx x y
convTerm' _   (VEmb _)          _        _        = False

-- | Eta expand value of function type.
etaLam :: Size ctx -> VElim ctx -> VTerm (S ctx)
etaLam s f = vemb (vapp (SS s) (sink f) (vemb (valZ s)))

-- | Typed conversion check, eliminations.
convElim :: ConvEnv ctx -> VElim ctx -> VElim ctx -> Bool
-- annotated terms: drop annotations.
convElim ctx (VAnn t ty)   e             = convTerm ctx ty t (vemb e)
convElim ctx e             (VAnn t ty)   = convTerm ctx ty (vemb e) t
convElim ctx (VNeu h1 sp1) (VNeu h2 sp2) = h1 == h2 && convSpine ctx (lookupEnv (lvlToIdx ctx.size h1) ctx.types) sp1 sp2
convElim _   _             _             = False

-- | Typed conversion check: spines.
convSpine :: forall ctx. ConvEnv ctx -> VTerm ctx -> Spine ctx -> Spine ctx -> Bool
convSpine ctx hty = bwd [] where
    bwd :: [SpinePart ctx] -> Spine ctx -> Spine ctx -> Bool
    bwd acc (VApp xs x) (VApp ys y) = bwd (PApp x y : acc) xs ys
    bwd acc (VSpl xs)   (VSpl ys)   = bwd (PSpl : acc) xs ys
    bwd acc VNil        VNil        = fwd hty acc
    bwd _   _           _           = False

    fwd :: VTerm ctx -> [SpinePart ctx] -> Bool
    fwd _          []              = True
    fwd (VPie a b) (PApp x y : zs) = convTerm ctx a x y && fwd (run ctx.size b (BElim (vann x a) Nothing)) zs
    fwd _          _               = False

-- /Verterbrae/
data SpinePart ctx
    = PApp (VTerm ctx) (VTerm ctx)
    | PSpl
  deriving Show

-- | Typed conversion: syntactic terms.
convSTerm :: ConvEnv ctx -> VTerm ctx -> STerm ctx -> STerm ctx -> Bool
convSTerm ctx ty x y =
    -- traceShow ("CONVS" :: String,ctx,ty,x,y) $
    convSTerm' ctx ty x y

-- | Typed conversion: syntactic terms.
convSTerm' :: ConvEnv ctx -> VTerm ctx -> STerm ctx -> STerm ctx -> Bool
convSTerm' _ VUni SUni SUni = True
convSTerm' _ _ _ _ = False -- TODO, more checks

-------------------------------------------------------------------------------
-- Type-checking context
-------------------------------------------------------------------------------

-- | Type checking ("linting") environment.
data LintEnv ctx ctx' = LintEnv
    { size   :: Size ctx'
    , values :: EvalEnv ctx ctx'
    , types  :: Env ctx (VTerm ctx')
    , types' :: Env ctx' (VTerm ctx')
    , stages :: Env ctx Stage
    , cstage :: Stage
    }

sinkLintEnv :: VTerm ctx' -> LintEnv ctx ctx' -> LintEnv ctx (S ctx')
sinkLintEnv t' (LintEnv s vs ts ts' ss cs) = LintEnv (SS s) (mapSink vs) (mapSink ts) (mapSink ts' :> sink t') ss cs

-- | Empty type checking environemnt.
emptyLintEnv :: LintEnv EmptyCtx EmptyCtx
emptyLintEnv = LintEnv SZ EmptyEnv EmptyEnv EmptyEnv EmptyEnv stage0

-- | Extend type checking environment with fresh variable.
bind :: LintEnv ctx ctx' -> VTerm ctx' -> LintEnv (S ctx) (S ctx')
bind ctx a = bind' (sinkLintEnv a ctx) (bvalZ ctx.size) (sink a)

-- | Extend type checking environment with a known value.
bind' :: LintEnv ctx ctx' -> BElim ctx' -> VTerm ctx' -> LintEnv (S ctx) ctx'
bind' (LintEnv s vs ts ts' ss cs) v t = LintEnv s (vs :> v) (ts :> t) ts' (ss :> cs) cs

-------------------------------------------------------------------------------
-- * Type-checking procedures
-------------------------------------------------------------------------------

-- | Checking: @Γ ⊢ B ∋ t@.
check :: LintEnv ctx ctx' -> Term ctx -> VTerm ctx' -> Either String ()
check ctx (Lam t)   (VPie a b) = do
    --
    --  x : A ⊢ B ∋ t
    -- --------------------------------- lam
    --        ⊢ Π (x : A) → B ∋ λ x → t
    --
    let ctx' = bind ctx a
    check ctx' t (runZ ctx.size b)
check _ctx (Lam _) ty         =
    Left $ "lam-not-pie " ++ show ty

check ctx (Pie a b) VUni = do
    --
    --        ⊢ U ∋ A
    --  x : A ⊢ U ∋ B
    -- --------------------------- pi
    --        ⊢ U ∋ Π (x : A) → B
    --
    check ctx a VUni
    let ctx' = bind ctx (evalTerm ctx.size ctx.values a)
    check ctx' b VUni
check _ctx (Pie _ _) ty =
    Left $ "Pi-not-U " ++ show ty

check _ctx Uni       VUni =
    --
    -- --------- type in type
    --  ⊢ U ∋ U
    --
    return ()
check _ctx Uni       ty =
    Left $ "U-not-U " ++ show ty

check ctx (Equ a x y) VUni = do
    --
    --  ⊢ A ∋ t
    --  ⊢ A ∋ s
    -- ---------------- identity
    --  ⊢ U ∋ Id A t s
    --
    check ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    check ctx x a'
    check ctx y a'
check _ctx (Equ _ _ _) ty = do
    Left $ "Id-not-U " ++ show ty

check ctx Rfl (VEqu a x y) = do
    --
    --  ⊢ A ∋ t ≡ s
    -- ------------------- refl
    --  ⊢ Id A t s ∋ refl
    --
    if convTerm (ConvEnv ctx.size ctx.types') a x y
    then return ()
    else Left $ "refl type-mismatch " ++ show (a, x, y)
check _ctx Rfl         ty =
    Left $ "refl-not-Id " ++ show ty

check _ One VUni = return ()
    --
    --
    -- ------------ unit
    --  ⊢ U ∋ Unit
    --
check _ One ty   = Left $ "1-not-U " ++ show ty

check _ Ast VOne = return ()
    --
    -- ------------ value
    --  ⊢ Unit ∋ *
check _ Ast ty   = Left $ "*-not-1 " ++ show ty

check ctx (Cod t) VUni = do
    --
    --  ⊢ Code [| U |] ∋ a
    -- -------------------- code
    --  ⊢ U ∋ Code a
    --
    check ctx t vcodUni
check _ (Cod _) ty = do
    Left $ "Cod-not-U " ++ show ty

check ctx (Quo t) (VCod a) = do
    --
    --  ⊢ ~ a ∋ t
    -- -------------------- quote
    --  ⊢ Code a ∋ [| t |]
    --
    check ctx { cstage = pred ctx.cstage } t (vsplCodArg ctx.size a)
check _ (Quo _) ty = do
    Left $ "Quo-not-Code " ++ show ty

check ctx (Emb e)   a = do
    --
    --  ⊢ e ∈ B
    --  ⊢ U ∋ A ≡ B
    -- ------------- emb
    --  ⊢ A ∋ e
    --
    b <- infer ctx e
    if convTerm (ConvEnv ctx.size ctx.types') VUni a b
    then return ()
    else Left $ "type-mismatch " ++ show (VUni, a, b)

-- | Inference or syntesis: @Γ ⊢ e ∈ A@
infer :: LintEnv ctx ctx' -> Elim ctx -> Either String (VTerm ctx')
infer ctx (Var i)   = do
    --
    --  (x : A) ∈ Γ
    -- ------------- var
    --  Γ ⊢ x ∈ A
    --
    let s = lookupEnv i ctx.stages
    when (s /= ctx.cstage) $ Left $ "stage mismatch " ++ show (s, ctx.cstage)
    return (lookupEnv i ctx.types)

infer ctx (App f t) = do
    --
    --  ⊢ f ∈ Π (x : A) → B
    --  ⊢ A ∋ t
    -- --------------------- app
    --  ⊢ f t ∈ B [x ↦ t]
    --
    ft <- infer ctx f
    case ft of
        VPie a b -> do
            check ctx t a
            let t' = evalTerm ctx.size ctx.values t
            return (run ctx.size b (BElim (vann t' a) Nothing))
        _ -> Left "Applying to not Pi"

infer ctx (Spl t) = do
    --
    --  ⊢ e ∈ Code A
    -- ------------------------------ splice
    --  ⊢ ~ e ∈ ~ (A : Code [| U |])
    --
    tt <- infer ctx { cstage = succ ctx.cstage } t
    case tt of
        VCod a -> do
            return (vsplCodArg ctx.size a)
        _ -> Left "Splicing not Code"

infer ctx (Ann t a) = do
    --
    --  ⊢ U ∋ A
    --  ⊢ A ∋ t
    -- --------------- ann
    --  ⊢ (t : A) ∈ A
    --
    check ctx a VUni
    let av = evalTerm ctx.size ctx.values a
    check ctx t av
    return av

infer ctx (Let t s) = do
    --
    --  ⊢ e ∈ A
    --  ⊢ f [x ↦ e] ∈ B
    -- ---------------------- let
    --  ⊢ let x = e in f ∈ B
    --
    tt <- infer ctx t
    let t' = evalElim ctx.size ctx.values t
    let ctx' = bind' ctx (BElim t' Nothing) tt
    infer ctx' s
