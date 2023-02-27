{-# LANGUAGE Safe #-}
module DeBruijn.Env (
    Env (EmptyEnv, (:>)),
    lookupEnv,
    sizeEnv,
    tabulateEnv,
) where

import Data.Kind (Type)

import DeBruijn.Ctx
import DeBruijn.Idx
import DeBruijn.Size

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
data Env ctx a where
    EmptyEnv :: Env EmptyCtx a
    (:>)     :: Env ctx a -> a -> Env (S ctx) a

infixl 5 :>

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Functor (Env ctx)

-- |
--
-- >>> toList (tabulateEnv S3 id)
-- [2,1,0]
--
deriving instance Foldable (Env ctx)

-- |
--
-- >>> traverse print (tabulateEnv S3 id)
-- 2
-- 1
-- 0
-- EmptyEnv :> () :> () :> ()
--
deriving instance Traversable (Env ctx)

instance Show a => Show (Env ctx a) where
    showsPrec _ EmptyEnv = showString "EmptyEnv"
    showsPrec d (xs :> x) = showParen (d > 5)
        $ showsPrec 5 xs
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
lookupEnv IZ     (_  :> x)  = x
lookupEnv (IS n) (xs :> _) = lookupEnv n xs

-- | Size of the environment.
--
-- >>> sizeEnv (EmptyEnv :> 'a' :> 'b')
-- 2
--
sizeEnv :: Env n a -> Size n
sizeEnv EmptyEnv  = SZ
sizeEnv (xs :> _) = SS (sizeEnv xs)

tabulateEnv :: Size ctx -> (Idx ctx -> a) -> Env ctx a
tabulateEnv SZ     _ = EmptyEnv
tabulateEnv (SS s) f = tabulateEnv s (f . IS) :> f IZ
