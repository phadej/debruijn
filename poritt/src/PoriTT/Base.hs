module PoriTT.Base (
    module X,
    pattern (:=),
    pattern TODO,
) where

import DeBruijn as X

import Control.Applicative        as X (liftA2, many, some, (<|>))
import Control.Monad              as X (guard, unless, void, when)
import Data.ByteString            as X (ByteString)
import Data.Coerce                as X (coerce)
import Data.Foldable              as X (foldl', for_, toList, traverse_)
import Data.Foldable.WithIndex    as X (ifor_)
import Data.Kind                  as X (Type)
import Data.List.NonEmpty         as X (NonEmpty (..))
import Data.Map.Strict            as X (Map)
import Data.Proxy                 as X (Proxy (..))
import Data.Semialign             as X (alignWith)
import Data.Semialign.Indexed     as X (ialignWith)
import Data.Set                   as X (Set)
import Data.String                as X (IsString (..))
import Data.Text                  as X (Text)
import Data.Text.Short            as X (ShortText)
import Data.These                 as X (These (..))
import Data.Traversable.WithIndex as X (ifor)
import Data.Word                  as X (Word8)
import Debug.Trace                as X
import GHC.Stack                  as X (HasCallStack)

pattern (:=) :: a -> b -> (a, b)
pattern a := b = (a, b)

infixr 0 :=

pattern TODO :: HasCallStack => () => a
pattern TODO <- _unused
  where TODO = error "TODO"

{-# COMPLETE TODO #-}
