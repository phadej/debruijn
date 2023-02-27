{-# LANGUAGE Unsafe #-}
module DeBruijn.Internal.Env (
    Env (EmptyEnv, (:>), UnsafeEnv),
    lookupEnv,
    sizeEnv,
    tabulateEnv,
) where

import Data.Coerce          (coerce)
import Data.Functor.Reverse (Reverse (..))
import Data.Kind            (Type)
import Data.SkewList.Lazy   (SkewList)
import Unsafe.Coerce        (unsafeCoerce)

import qualified Data.SkewList.Lazy as SL

import DeBruijn.Ctx
import DeBruijn.Internal.Idx
import DeBruijn.Internal.Size

-- $setup
-- >>> import DeBruijn
-- >>> import Data.Foldable (toList)

-------------------------------------------------------------------------------
-- Environment
-------------------------------------------------------------------------------

-- | Environment
--
-- >>> EmptyEnv :> 'a' :> 'b'
-- EmptyEnv :> 'a' :> 'b'
--
type Env :: Ctx -> Type -> Type
type role Env nominal representational
newtype Env ctx a = UnsafeEnv { unEnv :: SkewList a }

-------------------------------------------------------------------------------
-- Pattern synonyms
-------------------------------------------------------------------------------

-- We need a GADT to implement pattern synonyms.
type ViewEnv :: Ctx -> Type -> Type
type role ViewEnv nominal representational
data ViewEnv ctx a where
    EmptyViewEnv :: ViewEnv EmptyCtx a
    (:>>)     :: Env ctx a -> a -> ViewEnv (S ctx) a

viewEnv :: Env ctx a -> ViewEnv ctx a
viewEnv (UnsafeEnv env) = case SL.uncons env of
    Nothing      -> unsafeCoerce EmptyViewEnv
    Just (x, xs) -> unsafeCoerce (UnsafeEnv xs :>> x)

pattern EmptyEnv :: () => (ctx ~ EmptyCtx) => Env ctx a
pattern EmptyEnv <- (viewEnv -> EmptyViewEnv)
  where EmptyEnv = UnsafeEnv SL.Nil

infixl 5 :>
pattern (:>) :: () => (ctx ~ S ctx') => Env ctx' a -> a -> Env ctx a
pattern xs :> x <- (viewEnv -> xs :>> x)
  where xs :> x = UnsafeEnv (SL.cons x (unEnv xs))

{-# COMPLETE EmptyEnv, (:>) #-}

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Functor (Env ctx)

-- |
--
-- >>> toList (tabulateEnv S3 id)
-- [2,1,0]
--
instance Foldable (Env ctx) where
    foldMap f (UnsafeEnv xs) = foldMap f (Reverse xs)

-- |
--
-- >>> traverse print (tabulateEnv S3 id)
-- 2
-- 1
-- 0
-- EmptyEnv :> () :> () :> ()
--
instance Traversable (Env ctx) where
    traverse f (UnsafeEnv xs) = fmap (UnsafeEnv . getReverse) (traverse f (Reverse xs))

instance Show a => Show (Env ctx a) where
    showsPrec d0 (UnsafeEnv xs0) = go d0 xs0 where
        go d ys = case SL.uncons ys of
            Nothing      -> showString "EmptyEnv"
            Just (x, xs) -> showParen (d > 5)
                $ go 5 xs
                . showString " :> "
                . showsPrec 6 x

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

-- | Lookup in the context.
--
-- >>> lookupEnv IZ (EmptyEnv :> 'a' :> 'b')
-- 'b'
--
lookupEnv :: Idx ctx -> Env ctx a -> a
lookupEnv (UnsafeIdx i) (UnsafeEnv xs) = xs SL.! i

-- | Size of the environment.
--
-- >>> sizeEnv (EmptyEnv :> 'a' :> 'b')
-- 2
--
sizeEnv :: Env n a -> Size n
sizeEnv (UnsafeEnv xs) = UnsafeSize (length xs)

-- | Create 'Env' by creating elements given an 'Idx'.
--
-- >>> tabulateEnv S4 id
-- EmptyEnv :> 3 :> 2 :> 1 :> 0
--
tabulateEnv :: Size ctx -> (Idx ctx -> a) -> Env ctx a
tabulateEnv (UnsafeSize s) f = UnsafeEnv $ SL.fromList $ map (coerce f) [0 .. s - 1]
