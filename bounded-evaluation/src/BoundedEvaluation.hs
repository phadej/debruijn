{-# LANGUAGE RecursiveDo #-}
module BoundedEvaluation (
    eval,
    ev,
    conv,
    EvalEnv,
    emptyEvalEnv,
    Stats,
    newStats,
    printStats,
) where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Data.Hashable (Hashable (..))
import Data.HashSet (HashSet)

import qualified Data.HashSet as HS

import BoundedEvaluation.Base
import BoundedEvaluation.Term

-- $setup
-- >>> import BoundedEvaluation.Base
-- >>> import BoundedEvaluation.Term
-- >>> import BoundedEvaluation.Pretty

-------------------------------------------------------------------------------
-- Evaluation
-------------------------------------------------------------------------------

data Stats = Stats
    { allocs :: IORef Int
    , forces :: IORef Int
    , evals  :: IORef Int
    }

newStats :: IO Stats
newStats = do
    allocs <- newIORef 0
    forces <- newIORef 0
    evals  <- newIORef 0
    return Stats {..}

printStats :: Stats -> IO ()
printStats Stats {..} = do
    readIORef allocs >>= \v -> putStrLn $ "alloc: " ++ show v
    readIORef forces >>= \v -> putStrLn $ "force: " ++ show v
    readIORef evals  >>= \v -> putStrLn $ "evals: " ++ show v

type EvalEnv :: Ctx -> Ctx -> Type
type EvalEnv ctx ctx' = Env ctx (Ref ctx')

emptyEvalEnv :: EvalEnv EmptyCtx EmptyCtx
emptyEvalEnv = EmptyEnv

data Ref ctx = Ref !Bool !Int !(IORef (HeapObject ctx))
  deriving Eq
    
instance Hashable (Ref ctx) where
    hash (Ref _ i _) = i
    hashWithSalt s (Ref _ i _) = hashWithSalt s i

instance Sinkable Ref where mapLvl = error "needs unsafe sink"

instance Show (Ref ctx) where
    showsPrec d (Ref r n _) = showParen (d > 10) $ showString "Ref " . showsPrec 11 r . showChar ' ' . showsPrec 11 n

-- | Heap objects.
data HeapObject ctx
    = HThunk !(Closure ctx)
    | HValue !(Value ctx)
    | HBlackHole

-- |
data Value ctx
    = VZer
    | VSuc !(Ref ctx)
    | VLam !(Closure1 ctx)
    | VNeu !(Lvl ctx) !(Spine ctx)

type Spine :: Ctx -> Type
data Spine ctx
    = VNil
    | VApp !(Spine ctx) !(Ref ctx)
    | VMch !(Spine ctx) !(Ref ctx) !(Closure1 ctx)

deriving instance Show (Value ctx)
deriving instance Show (Spine ctx)

data Closure ctx where
    Closure :: EvalEnv ctx ctx' -> Term ctx -> Closure ctx'

data Closure1 ctx where
    Closure1 :: EvalEnv ctx ctx' -> Term (S ctx) -> Closure1 ctx'

deriving instance Show (Closure ctx)
deriving instance Show (Closure1 ctx)

force :: Stats -> Ref ctx -> IO (Value ctx)
force q reee@(Ref r _ ref) = do
    when r $ putStrLn $ "forcing recursive ref " ++ show reee
    n <- atomicModifyIORef' q.forces (\n -> (n + 1, n))
    when (n >= 1_000) $ fail "maximum force"
    o <- readIORef ref
    case o of
        HBlackHole             -> fail "forcing blackhole"
        HValue v               -> return v
        HThunk (Closure env t) -> do
            putStrLn $ "force HThunk: " ++ show t
            writeIORef ref HBlackHole
            v <- eval q env t
            writeIORef ref (HValue v)
            return v

-- TOOD: Bool -> data Recursive = Recursive | NonRecursive
allocHeapObject :: Bool -> Stats -> HeapObject ctx -> IO (Ref ctx)
allocHeapObject r q h = do
    n <- atomicModifyIORef' q.allocs (\n -> (n + 1, n))
    Ref r n <$> newIORef h

refZer :: Ref ctx
refZer = unsafePerformIO $ Ref False (-1) <$> newIORef (HValue VZer)
{-# NOINLINE refZer #-}

makeRef :: Bool -> Stats -> EvalEnv ctx ctx' -> Term ctx -> IO (Ref ctx')
makeRef _ _ _   Zer     = return refZer
makeRef r q env (Lam t) = allocHeapObject r q (HValue (VLam (Closure1 env t)))
makeRef r q env t       = allocHeapObject r q (HThunk (Closure env t))

ev :: EvalEnv ctx ctx' -> Term ctx -> IO (Value ctx')
ev env t = do
    stats <- newStats
    v <- eval stats env t
    printStats stats
    return v

-- |
--
-- >>> q <- newStats
--
-- >>> eval q emptyEvalEnv two
-- VSuc (Ref 0)
--
-- >>> eval q emptyEvalEnv ex1
-- VSuc (Ref 13)
--
-- >>> eval q EmptyEnv ex4
-- *** Exception: user error (forcing blackhole)
--
eval :: Stats -> EvalEnv ctx ctx' -> Term ctx -> IO (Value ctx')
eval q env t = do
    n <- atomicModifyIORef' q.evals (\n -> (n + 1, n))
    when (n >= 1_000) $ fail "maximum evals"
    eval' q env t

eval' :: Stats -> EvalEnv ctx ctx' -> Term ctx -> IO (Value ctx')
eval' q env (Var x) = do
    force q (lookupEnv x env)
eval' _ env (Lam t) = do
    return (VLam (Closure1 env t))
eval' q env (App f t) = do
    t' <- makeRef False q env t
    f' <- eval q env f
    vApp q f' t'
eval' _ _   Zer = do
    return VZer
eval' q env (Suc t) = do
    t' <- makeRef False q env t
    return (VSuc t')
eval' q env (Let t s) = do
    t' <- makeRef False q env t
    eval q (env :> t') s
eval' q env (Fix t) = mdo
    t' <- makeRef True q (env :> t') t
    force q t'
eval' q env (Mch t n s) = do
    t' <- eval q env t
    n' <- makeRef False q env n
    s' <- return (Closure1 env s)
    vMch q t' n' s'

vApp :: Stats -> Value ctx' -> Ref ctx' -> IO (Value ctx')
vApp q (VLam t)    x = evalClosure1 q t x
vApp _ (VNeu l sp) x = return (VNeu l (VApp sp x ))
vApp _ VZer {}     _ = fail "apply to zero"
vApp _ VSuc {}     _ = fail "apply to succ"

vMch :: Stats -> Value ctx -> Ref ctx -> Closure1 ctx -> IO (Value ctx)
vMch q VZer        n _ = force q n
vMch q (VSuc m)    _ s = evalClosure1 q s m
vMch _ (VNeu l sp) n s = return (VNeu l (VMch sp n s))
vMch _ VLam {}     _ _ = fail "case lambda"

evalClosure1 :: Stats -> Closure1 ctx -> Ref ctx -> IO (Value ctx)
evalClosure1 q (Closure1 env t) ref = eval q (env :> ref) t

stuckClosure1 :: Stats -> Size ctx -> Closure1 ctx -> IO (Value (S ctx))
stuckClosure1 q s (Closure1 env t) = do
    x <- allocHeapObject False q (HValue (VNeu (lvlZ s) VNil))
    eval q (mapSink env :> x) t

-------------------------------------------------------------------------------
-- Quoting
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Conversion checking
-------------------------------------------------------------------------------

-- | Conversion checking
--
-- >>> q <- newStats
-- >>> x <- eval q emptyEvalEnv two
--
-- >>> conv q SZ x x
-- True
--
-- >>> v1  <- eval q emptyEvalEnv ex1
-- >>> v2  <- eval q emptyEvalEnv ex2
-- >>> v3a <- eval q emptyEvalEnv ex3
-- >>> v3b <- eval q emptyEvalEnv ex3
--
-- >>> conv q SZ v1 v1
-- True
--
-- >>> conv q SZ v1 v2
-- True
--
-- >>> conv q SZ v1 v3a
-- False
--
-- >>> conv q SZ v3a v3b
-- True
--
-- >>> vInd <- eval q emptyEvalEnv ind
-- >>> conv q SZ vInd vInd
-- *** Exception: user error (maximum evals)
--
conv :: Stats -> Size ctx -> Value ctx -> Value ctx -> IO Bool
conv q s x y = do
    v <- newIORef HS.empty
    conv' q v s x y

type Visited = IORef (HashSet (Int, Int))

conv' :: Stats -> Visited -> Size ctx -> Value ctx -> Value ctx -> IO Bool
conv' _ _ _ VZer      VZer      =
    return True
conv' _ _ _ VZer      _         =
    return False
conv' q v s (VSuc t1) (VSuc t2) = do
    convRef q v s t1 t2
conv' _ _ _ (VSuc _)  _         = return False
conv' q v s (VLam c1) (VLam c2) = do
    convClosure1 q v s c1 c2
conv' _ _ _ (VLam _)      _             =
    return False
conv' q v s (VNeu l1 sp1) (VNeu l2 sp2) = do
    if l1 == l2
    then convSpine q v s sp1 sp2
    else return False
conv' _ _ _ (VNeu _ _) _         =
    return False

convRef :: Stats -> Visited -> Size ctx -> Ref ctx -> Ref ctx -> IO Bool
convRef q v s t1@(Ref r1 i1 _) t2@(Ref r2 i2 _) = do
    print $ "convRef " ++ show (t1, t2)
    let k = (i1, i2)
    hs <- readIORef v
    if HS.member k hs
    then do
        return True
    else do
        writeIORef v (HS.insert k hs)
        print (t1, t2)
        v1 <- force q t1
        v2 <- force q t2
        conv' q v s v1 v2

convClosure1 :: Stats -> Visited -> Size ctx -> Closure1 ctx -> Closure1 ctx -> IO Bool
convClosure1 q v s c1 c2 = do
    v1 <- stuckClosure1 q s c1
    v2 <- stuckClosure1 q s c2
    conv' q v (SS s) v1 v2

convSpine :: Stats -> Visited -> Size ctx -> Spine ctx -> Spine ctx -> IO Bool
convSpine _ _ _ VNil VNil =
    return True
convSpine _ _ _ VNil _ =
    return False
convSpine q v s (VApp sp1 t1) (VApp sp2 t2) = do
    convSpine q v s sp1 sp2 .&&. convRef q v s t1 t2
convSpine _ _ _ (VApp _ _) _ =
    return False
convSpine q v s (VMch sp1 n1 s1) (VMch sp2 n2 s2) =
    convSpine q v s sp1 sp2 .&&. convRef q v s n1 n2 .&&. convClosure1 q v s s1 s2
convSpine _ _ _ (VMch _ _ _) _ =
    return False
