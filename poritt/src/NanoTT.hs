-- | NanoTT is one module implementation of most things happening.
module NanoTT where

import PoriTT.Base

-------------------------------------------------------------------------------
-- Term & Elim
-------------------------------------------------------------------------------
--
-- | Term types are checked
type Term :: Ctx -> Type
data Term ctx where
    Pie :: Term ctx -> Term (S ctx) -> Term ctx
    Lam :: Term (S ctx) -> Term ctx
    Uni :: Term ctx
    Emb :: Elim ctx -> Term ctx

    -- extras
    Equ :: Term ctx -> Term ctx -> Term ctx -> Term ctx  -- Id A x y : U
    Rfl :: Term ctx                                      -- refl : Id A x y
    One :: Term ctx                                      -- 1 : U
    Ast :: Term ctx                                      -- * : 1

-- | Elimination types are inferred
type Elim :: Ctx -> Type
data Elim ctx where
   Var :: Idx ctx -> Elim ctx
   App :: Elim ctx -> Term ctx -> Elim ctx
   Ann :: Term ctx -> Term ctx -> Elim ctx
   Let :: Elim ctx -> Elim (S ctx) -> Elim ctx

deriving instance Show (Term ctx)
deriving instance Show (Elim ctx)

-------------------------------------------------------------------------------
-- Closures and evaluation environment
-------------------------------------------------------------------------------

type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (VElim ctx')

type Closure :: Ctx -> Type
data Closure ctx' where Closure :: EvalEnv ctx ctx' -> Term (S ctx) -> Closure ctx'

deriving instance Show (Closure ctx)

run :: Size ctx -> Closure ctx -> VElim ctx -> VTerm ctx
run s (Closure env f) t = evalTerm s (env :> t) f

runZ :: Size ctx -> Closure ctx -> VTerm (S ctx)
runZ s clos = run (SS s) (sink clos) (valZ s)

valZ :: Size ctx -> VElim (S ctx)
valZ s = VNeu (lvlZ s) VNil

instance Sinkable Closure where mapLvl = error "omitted"

-------------------------------------------------------------------------------
-- Values
-------------------------------------------------------------------------------

type VTerm :: Ctx -> Type
data VTerm ctx where
    VPie :: VTerm ctx -> Closure ctx -> VTerm ctx
    VLam :: Closure ctx -> VTerm ctx
    VUni :: VTerm ctx
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

deriving instance Show (VTerm ctx)
deriving instance Show (VElim ctx)
deriving instance Show (Spine ctx)

instance Sinkable VTerm where mapLvl = error "omitted"
instance Sinkable VElim where mapLvl = error "omitted"
instance Sinkable Spine where mapLvl = error "omitted"

-------------------------------------------------------------------------------
-- Evaluation: Term -> VTerm, Elim -> VElim
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

evalElim :: Size ctx' -> EvalEnv ctx ctx' -> Elim ctx -> VElim ctx'
evalElim _ env (Var x)   = lookupEnv x env
evalElim s env (Ann t a) = vann (evalTerm s env t) (evalTerm s env a)
evalElim s env (Let t r) = evalElim s (env :> evalElim s env t) r
evalElim s env (App f t) = vapp s (evalElim s env f) (evalTerm s env t)

-------------------------------------------------------------------------------
-- Reductions
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
    in vann (run s closT r') (run s closB r')
vapp s (VAnn (VEmb e) _)                  r = vapp s e r
vapp _ (VAnn (VLam _) ty)                 _ = VErr $ "lambda annotated with " ++ show ty
vapp _ (VAnn f _)                         _ = VErr $ "applying not lambda" ++ show f
vapp _ (VErr msg)                         _ = VErr msg
vapp _ (VNeu h sp)                        r = VNeu h (VApp sp r)

-------------------------------------------------------------------------------
-- Normal forms
-------------------------------------------------------------------------------

type Nf :: Ctx -> Type
data Nf ctx where
    NLam :: Nf (S ctx) -> Nf ctx
    NPie :: Nf ctx -> Nf (S ctx) -> Nf ctx
    NUni :: Nf ctx
    Neut :: Ne ctx -> Nf ctx

type Ne :: Ctx -> Type
data Ne ctx where
    NVar :: Idx ctx -> Ne ctx
    NApp :: Ne ctx -> Nf ctx -> Ne ctx

-------------------------------------------------------------------------------
-- Quoting
-------------------------------------------------------------------------------

quoteElim :: Size ctx -> VElim ctx -> Either String (Nf ctx)
quoteElim _ (VErr msg)  = Left msg
quoteElim s (VAnn t _)  = quoteTerm s t
quoteElim s (VNeu l sp) = Neut <$> quoteSp s (pure (NVar (lvlToIdx s l))) sp

quoteTerm :: Size ctx -> VTerm ctx -> Either String (Nf ctx)
quoteTerm _ VUni       = pure NUni
quoteTerm s (VEmb e)   = quoteElim s e
quoteTerm s (VPie a b) = NPie <$> quoteTerm s a <*> quoteTerm (SS s) (runZ s b)
quoteTerm s (VLam t)   = NLam <$> quoteTerm (SS s) (runZ s t)
quoteTerm _ VEqu {}    = error "not implemented"
quoteTerm _ VRfl {}    = error "not implemented"
quoteTerm _ VOne {}    = error "not implemented"
quoteTerm _ VAst {}    = error "not implemented"

quoteSp :: Size ctx -> Either String (Ne ctx) -> Spine ctx -> Either String (Ne ctx)
quoteSp _ h VNil        = h
quoteSp s h (VApp sp e) = NApp <$> quoteSp s h sp <*> quoteTerm s e

-------------------------------------------------------------------------------
-- Conversion checking
-------------------------------------------------------------------------------

type TypeEnv ctx ctx' = Env ctx (VTerm ctx')

-- | Typed conversion check.
--
-- @convTerm s Γ x y t@ checks @Γ ⊢ x ≡ y : t@
convTerm :: Size ctx -> TypeEnv ctx ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Bool
convTerm s env x y ty = {- traceShow ("CONV",env,x,y,ty) -} (convTerm' s env x y ty)

convTerm' :: Size ctx -> TypeEnv ctx ctx -> VTerm ctx -> VTerm ctx -> VTerm ctx -> Bool
convTerm' _ _   VUni            VUni            _             = True
convTerm' s env (VLam t1)       (VLam t2)       (VPie a b)    = convTerm (SS s) (mapSink env :> sink a) (runZ s t1) (runZ s t2) (runZ s b)
convTerm' s env (VPie a1 b1)    (VPie a2 b2)    _             = convTerm s env a1 a2 VUni && convTerm (SS s) (mapSink env :> sink a1) (runZ s b1) (runZ s b2) VUni
convTerm' _ _   VOne            VOne            _             = True
convTerm' s env (VEqu a1 x1 y1) (VEqu a2 x2 y2) _             = convTerm s env a1 a2 VUni && convTerm s env x1 x2 a1 && convTerm s env y1 y2 a1
-- eta-expansion for lambda
convTerm' s env t1              t2              ty@(VPie a b) = convTerm (SS s) (mapSink env :> sink a) (etaLam s t1 ty) (etaLam s t2 ty) (runZ s b)
-- eta-expansion for 1 and Id x a y
convTerm' _ _   _               _               VEqu {}       = True -- all refls are equal. UIP.
convTerm' _ _   _               _               VOne          = True -- all 1 terms are equal
-- then we try neutral terms
convTerm' s env (VEmb e1)       (VEmb e2)       ty            = convElim s env e1 e2 ty
-- other things are not convertible
convTerm' _ _   _               _               _             = False

-- eta-expand term: t ~~> \x -> t x
etaLam :: Size ctx -> VTerm ctx -> VTerm ctx -> VTerm (S ctx)
etaLam s t a = vemb (vapp (SS s) (sink (vann t a)) (vemb (valZ s)))

convElim :: Size ctx -> TypeEnv ctx ctx -> VElim ctx -> VElim ctx -> VTerm ctx -> Bool
-- annotated terms: drop annotations.
convElim s env (VAnn t1 _)   (VAnn t2 _)   ty      = convTerm s env t1 t2 ty
-- eta-expansions:
convElim _ _   _             _             VEqu {} = True
convElim _ _   _             _             VOne    = True
-- neutral elements
convElim s env (VNeu h1 sp1) (VNeu h2 sp2) _       = h1 == h2 && convSpine s env (lookupEnv (lvlToIdx s h1) env) sp1 sp2
convElim _ _   _             _             _       = False

convSpine :: forall ctx. Size ctx -> TypeEnv ctx ctx -> VTerm ctx -> Spine ctx -> Spine ctx -> Bool
convSpine s env hty = bwd [] where
    bwd :: [(VTerm ctx, VTerm ctx)] -> Spine ctx -> Spine ctx -> Bool
    bwd acc (VApp xs x) (VApp ys y) = bwd ((x,y) : acc) xs ys
    bwd acc VNil        VNil        = fwd acc hty
    bwd _   _           _           = False

    fwd :: [(VTerm ctx, VTerm ctx)] -> VTerm ctx -> Bool
    fwd []            _          = True
    fwd ((x, y) : zs) (VPie a b) = convTerm s env x y a && fwd zs (run s b (VAnn x a))
    fwd (_      : _)  _          = False

-------------------------------------------------------------------------------
-- Type-checking
-------------------------------------------------------------------------------

data LintCtx ctx ctx' = LintCtx
    { size   :: Size ctx'
    , values :: EvalEnv ctx ctx'
    , types  :: Env ctx (VTerm ctx')
    , types' :: Env ctx' (VTerm ctx')
    }

sinkLintCtx :: VTerm ctx' -> LintCtx ctx ctx' -> LintCtx ctx (S ctx')
sinkLintCtx t' (LintCtx s vs ts ts') = LintCtx (SS s) (mapSink vs) (mapSink ts) (mapSink ts' :> sink t')

emptyLintCtx :: LintCtx EmptyCtx EmptyCtx
emptyLintCtx = LintCtx SZ EmptyEnv EmptyEnv EmptyEnv

bind :: LintCtx ctx ctx' -> VTerm ctx' -> LintCtx (S ctx) (S ctx')
bind ctx a = bind' (sinkLintCtx a ctx) (valZ (size ctx)) (sink a)

bind' :: LintCtx ctx ctx' -> VElim ctx' -> VTerm ctx' -> LintCtx (S ctx) ctx'
bind' (LintCtx s vs ts ts') v t = LintCtx s (vs :> v) (ts :> t) ts'

check :: LintCtx ctx ctx' -> Term ctx -> VTerm ctx' -> Either String ()
check ctx (Lam t)   (VPie a b) = do
    let ctx' = bind ctx a
    check ctx' t (runZ ctx.size b)
check _ctx (Lam _) ty         =
    Left $ "lam-not-pie " ++ show ty
check ctx (Pie a b) VUni = do
    check ctx a VUni
    let ctx' = bind ctx (evalTerm ctx.size ctx.values a)
    check ctx' b VUni
check _ctx (Pie _ _) ty =
    Left $ "Pi-not-U " ++ show ty
check _ctx Uni       VUni =
    return ()
check _ctx Uni       ty =
    Left $ "U-not-U " ++ show ty
check ctx (Emb e)   a = do
    b <- infer ctx e
    if convTerm ctx.size ctx.types' a b VUni
    then return ()
    else Left $ "type-mismatch " ++ show (a, b)

check ctx (Equ a x y) VUni = do
    check ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    check ctx x a'
    check ctx y a'
check _ctx (Equ _ _ _) ty = do
    Left $ "Id-not-U " ++ show ty
check ctx Rfl (VEqu a x y) = do
    if convTerm ctx.size ctx.types' x y a
    then return ()
    else Left $ "refl type-mismatch " ++ show (x, y)
check _ctx Rfl         ty =
    Left $ "refl-not-Id " ++ show ty
check _ One VUni = return ()
check _ One ty   = Left $ "1-not-U " ++ show ty
check _ Ast VOne = return ()
check _ Ast ty   = Left $ "*-not-1 " ++ show ty

infer :: LintCtx ctx ctx' -> Elim ctx -> Either String (VTerm ctx')
infer ctx (Var i)   =
    Right (lookupEnv i ctx.types)
infer ctx (Ann t a) = do
    check ctx a VUni
    let av = evalTerm ctx.size ctx.values a
    check ctx t av
    return av
infer ctx (App f t) = do
    ft <- infer ctx f
    case ft of
        VPie a b -> do
            check ctx t a
            let t' = evalTerm ctx.size ctx.values t
            return (run ctx.size b (VAnn t' a))
        _ -> Left "Applying to not Pi"
infer ctx (Let t s) = do
    tt <- infer ctx t
    let t' = evalElim ctx.size ctx.values t
    let ctx' = bind' ctx t' tt
    infer ctx' s
