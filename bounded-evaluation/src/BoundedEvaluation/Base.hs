module BoundedEvaluation.Base (
    module X,
    type (:=),
    pattern (:=),
    pattern TODO,
    pattern NZ, pattern NS,
    (.&&.),
) where

import DeBruijn as X

import Control.Applicative as X (Alternative (many, some, (<|>)), asum, liftA2, (<**>))
import Control.Monad       as X (guard, unless, void, when)
import Data.Coerce         as X (coerce)
import Data.Foldable       as X (foldl', for_, toList, traverse_)
import Data.Function       as X ((&))
import Data.Kind           as X (Type)
import Data.List.NonEmpty  as X (NonEmpty (..))
import Data.Proxy          as X (Proxy (..))
import Data.String         as X (IsString (..))
import Data.Traversable    as X (for)
import Data.Word           as X (Word8)
import Debug.Trace         as X
import GHC.Generics        as X (Generic)
import GHC.Stack           as X (HasCallStack)
import Numeric.Natural     as X (Natural)

type a := b = (a, b)

pattern (:=) :: a -> b -> a := b
pattern a := b = (a, b)

infixr 0 :=

pattern TODO :: HasCallStack => () => a
pattern TODO <- _unused
  where TODO = error "TODO"

{-# COMPLETE TODO #-}

pattern NZ :: Natural
pattern NZ = 0

pattern NS :: Natural -> Natural
pattern NS n <- (safePred -> Just n)
  where NS n = n + 1

safePred :: Natural -> Maybe Natural
safePred 0 = Nothing
safePred n = Just (n - 1)

{-# COMPLETE NZ, NS #-}

(.&&.) :: Monad m => m Bool -> m Bool -> m Bool
x .&&. y = do
    x' <- x
    if x' then y else return False
