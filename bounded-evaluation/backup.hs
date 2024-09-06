{-# LANGUAGE RecursiveDo #-}
module BoundedEvaluation (
    STG,
    toSTG,
    simpl,
    eval,
    conv,
) where

import Data.IORef

import BoundedEvaluation.Base
import BoundedEvaluation.Pretty
import BoundedEvaluation.Term

-- $setup
-- >>> import BoundedEvaluation.Base
-- >>> import BoundedEvaluation.Term
-- >>> import BoundedEvaluation.Pretty

-------------------------------------------------------------------------------
-- * STG
-------------------------------------------------------------------------------

type STG :: Ctx -> Type
data STG ctx where
    SLet :: Bind ctx -> STG (S ctx) -> STG ctx
    SRec :: Bind (S ctx) -> STG (S ctx) -> STG ctx
    SApp :: Idx ctx -> [Atom ctx] -> STG ctx
    SZer :: STG ctx
    SSuc :: Atom ctx -> STG ctx
    SWkn :: Wk ctx ctx' -> STG ctx -> STG ctx'
    SSpl :: STG ctx -> STG ctx -> STG (S ctx) -> STG ctx

type Bind :: Ctx -> Type
data Bind ctx where
    Bind :: Binder ctx ctx' -> STG ctx' -> Bind ctx

data Binder ctx ctx' where
    BZ :: Binder ctx ctx
    BS :: Binder ctx ctx' -> Binder ctx (S ctx')

type Atom :: Ctx -> Type
data Atom ctx where
    AVar :: Idx ctx -> Atom ctx

deriving instance Show (STG ctx)
deriving instance Show (Bind ctx)
deriving instance Show (Binder ctx ctx')
deriving instance Show (Atom ctx)

instance Weaken STG where
    weaken wk (SWkn wk' t) = SWkn (compWk wk' wk) t
    weaken wk t            = SWkn wk t

instance Weaken Bind where
    weaken w (Bind b t) = keepBinder b w $ \b' w' -> Bind b' (weaken w' t) where

keepBinder
    :: Binder n m
    -> Wk n p
    -> (forall q. Binder p q -> Wk m q -> r)
    -> r
keepBinder BZ     w kont = kont BZ w
keepBinder (BS b) w kont = keepBinder b w $ \b' w' -> kont (BS b') (KeepWk w')

aux :: Binder (S ctx) ctx' -> Binder ctx ctx'
aux BZ     = BS BZ
aux (BS b) = BS (aux b)

keepB :: Binder ctx ctx' -> Binder (S ctx) (S ctx')
keepB BZ = BZ
keepB (BS b) = BS (keepB b)


-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty STG where
    pretty env (SLet t s) = withFresh "x" $ \x ->
        prettyLet (env :> x) (prettyBind x env t :) s
    pretty _   SZer       = "zero"
    pretty env (SSuc n)   = ppList1 "succ" [pretty env n]
    pretty env (SWkn w t) = pretty (weakenEnv w env) t
    pretty env (SRec t s) = withFresh "r" $ \r ->
        prettyLet (env :> r) (prettyBind (ppList1 "rec" [r]) (env :> r) t :) s
    pretty env (SSpl t n s) = withFresh "n" $ \m -> ppList1 "case"
        [ pretty env t
        , ppList1 "zero"               [pretty env n]
        , ppList1 (ppList1 "succ" [m]) [pretty (env :> m) s]
        ]
    pretty env (SApp i ts) = ppList1 (lookupEnv i env) (map (pretty env) ts)

prettyBind :: Doc -> Env ctx Doc -> Bind ctx -> Doc
prettyBind name env (Bind binder t) = go binder $ \xs f ->
    ppList1 name [ppList (xs []), pretty (f env) t]
  where
    go :: Binder ctx ctx' -> (([Doc] -> [Doc]) -> (Env ctx Doc -> Env ctx' Doc) -> Doc) -> Doc
    go BZ     kont = kont id id
    go (BS b) kont = withFresh "x" $ \x -> go b $ \xs f -> kont (xs . (x :)) (\e -> f e :> x)

instance Pretty Atom where
    pretty env (AVar x) = lookupEnv x env

prettyLet :: Env ctx Doc -> ([Doc] -> [Doc]) -> STG ctx -> Doc
prettyLet env xs (SLet t s) = withFresh "x" $ \x -> prettyLet (env :> x) (xs . (prettyBind x env t :)) s
prettyLet env xs t          = ppList1 "let" (xs [pretty env t])

-------------------------------------------------------------------------------
-- Conversion
-------------------------------------------------------------------------------

-- |
--
-- x >>> pretty EmptyEnv $ toSTG SZ two
-- (let (x_0 zero) (x_1 (succ x_0)) (succ x_0))
--
-- x >>> toSTG SZ ind
--
-- x >>> pretty EmptyEnv $ toSTG SZ ex1
--
toSTG :: Size ctx -> Term ctx -> STG ctx
toSTG _ (Var x) =
    SApp x []
toSTG s (App f t) =
    sLet (sThk (toSTG s f)) $
    sLet (sThk (weaken wk1 (toSTG s t))) $
    SApp (IS IZ) [AVar IZ]
toSTG s (Lam t) =
    sLet (sLam (toSTG (SS s) t)) $
    SApp IZ []
toSTG s (Let t e) =
    sLet (sThk (toSTG s t)) $
    toSTG (SS s) e
toSTG x (Fix t) =
    sRec (sThk (toSTG (SS x) t)) $
    SApp IZ []
toSTG _ Zer =
    SZer
toSTG s (Suc n) =
    sLet (sThk (toSTG s n)) $
    SSuc (AVar IZ)
toSTG x (Spl t n s) =
    SSpl (toSTG x t) (toSTG x n) (toSTG (SS x) s)

sThk :: STG ctx -> Bind ctx
sThk (SLet (Bind b c) (SApp IZ [])) = Bind b c
sThk t                              = Bind BZ t

sLam :: STG (S ctx) -> Bind ctx
sLam (SLet (Bind b c) (SApp IZ [])) = Bind (aux b) c
sLam t                              = Bind (BS BZ) t


sLet :: Bind ctx -> STG (S ctx) -> STG ctx
sLet b t = SLet b t

sRec :: Bind (S ctx) -> STG (S ctx) -> STG ctx
sRec b t = SRec b t

simpl :: Env ctx (STG ctx') -> STG ctx -> STG ctx'
simpl = undefined

-------------------------------------------------------------------------------
-- Evaluation
-------------------------------------------------------------------------------

type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (HeapObject ctx')

-- |
data Val ctx
    = VZer
    | VSuc !(HeapObject ctx)
    | VLam !(LamClosure ctx)
    | VNeu !(Lvl ctx) ()

deriving instance Show (Val ctx)

-- | Heap objects.
data HeapObject ctx
    = Thunk !(IORef (Either (Closure ctx) (Val ctx)))
    | HLam !(LamClosure ctx)
    | HNeu !(Lvl ctx) ()

instance Show (HeapObject ctx) where
    showsPrec _ Thunk {} = showString "Thunk"
    showsPrec _ HLam {} = showString "HLam"
    showsPrec _ HNeu {} = showString "HNeu"

data Closure ctx where
    Closure :: EvalEnv ctx ctx' -> STG ctx -> Closure ctx'

data LamClosure ctx where
    LamClosure :: EvalEnv ctx ctx' -> Binder ctx ctx'' -> STG ctx'' -> LamClosure ctx'

deriving instance Show (LamClosure ctx)

mkHeapObject :: EvalEnv ctx ctx' -> Bind ctx -> IO (HeapObject ctx')
mkHeapObject env (Bind BZ t) = do
    ref <- newIORef $ Left $ Closure env t
    return (Thunk ref)
mkHeapObject env (Bind b t) =
    return (HLam (LamClosure env b t))

evalAtom :: EvalEnv ctx ctx' -> Atom ctx -> HeapObject ctx'
evalAtom env (AVar i) = lookupEnv i env

eval :: EvalEnv ctx ctx' -> STG ctx -> IO (Val ctx')
eval env (SWkn w t) = eval (weakenEnv w env) t
eval _   SZer       = return VZer
eval env (SSuc x)   = do
    let o = evalAtom env x
    return (VSuc o)
eval env (SLet b t) = do
    o <- mkHeapObject env b
    eval (env :> o) t
eval env (SRec b t) = mdo
    o <- mkHeapObject (env :> o) b
    eval (env :> o) t
eval env (SApp x []) = do
    force (lookupEnv x env)
eval env (SApp x args) = do
    f <- force (lookupEnv x env)
    vApps f $ map (evalAtom env) args
eval env (SSpl t n s) = do
    t' <- eval env t
    case t' of
        VZer   -> eval env n
        VSuc m -> eval (env :> m) s
        VLam {} -> fail "case on lambda"
        VNeu {} -> fail "TODO: vSpl VNeu"

vApps :: Val ctx -> [HeapObject ctx] -> IO (Val ctx)
vApps (VLam (LamClosure env b t)) args = vApps' env b t args
vApps (VNeu {}) _ = fail "TODO: vApps VNeu"
vApps VZer {}   _ = fail "apply to zero"
vApps VSuc {}   _ = fail "apply to succ"

vApps' :: EvalEnv ctx ctx' -> Binder ctx ctx'' -> STG ctx'' -> [HeapObject ctx'] -> IO (Val ctx')
vApps' env   BZ     f []       = eval env f
vApps' env   BZ     f ts@(_:_) = do
    v <- eval env f
    error "TODO-BZ" v ts
vApps' env b@(BS _) f []       = return (VLam (LamClosure env b f))
vApps' env   (BS b) f (t:ts)   = vApps' (env :> t) (keepB b) f ts


force :: HeapObject ctx -> IO (Val ctx)
force (Thunk ref) = do
    x <- readIORef ref
    -- TODO: write blackhole
    case x of
        Right v -> return v
        Left (Closure env t) -> do
            v <- eval env t
            writeIORef ref (Right v)
            return v
force (HLam c) = return (VLam c)
force (HNeu l sp) = return (VNeu l sp)

-------------------------------------------------------------------------------
-- Conversion checking
-------------------------------------------------------------------------------

-- | Conversion checking
--
-- >>> x <- eval EmptyEnv $ toSTG SZ two
-- >>> x
-- VSuc Thunk
--
-- >>> conv x x
-- True
--
conv :: Val ctx -> Val ctx -> IO Bool
conv VZer      VZer      = return True
conv VZer      _         = return False
conv (VSuc t1) (VSuc t2) = do
    v1 <- force t1
    v2 <- force t2
    conv v1 v2
conv (VSuc _)  _         = return False
conv (VLam _) (VLam _) = error "TODOlam"
conv (VLam _) _ = return False

conv (VNeu _ _) (VNeu _ _) = error "TODOneu"
conv (VNeu _ _) _         = return False

