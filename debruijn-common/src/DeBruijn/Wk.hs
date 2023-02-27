{-# LANGUAGE Safe #-}
module DeBruijn.Wk (
    Wk(IdWk, SkipWk, KeepWk),
    -- * Combinators
    wk1,
    compWk,
    -- * Index weakening
    weakenIdx,
    -- * Size weakening
    weakenSize,
    contractSize,
    -- * Environment contraction
    weakenEnv,
    setWeakenEnv,
    overWeakenEnv,
) where

import Data.Kind (Type)

import DeBruijn.Ctx
import DeBruijn.Env
import DeBruijn.Idx
import DeBruijn.Size

-- $setup
-- >>> :set -XGADTs
-- >>> import DeBruijn
-- >>> import Data.Function ((&))
-- >>> import Data.Char (toUpper)

-- | Weakenings, order preserving embeddings.
--
-- @Wk n m@ could be represented as @m@ bit field with popCount of @n@.
--
-- Constructor names make sense when you look at the implementation of 'weakenEnv'.
--
-- Note: usually 'ViewWk is defined as
--
-- @
-- data Wk ctx ctx' where
--     WkNil  :: Wk EmptyCtx EmptyCtx
--     KeepWk :: Wk ctx ctx' -> Wk (S ctx)  (S ctx')
--     SkipWk :: Wk ctx ctx' -> Wk    ctx   (S ctx')
-- @
--
-- However that representation doesn't allow to make @'wkId' :: 'ViewWk ctx ctx@ without knowing the size of context.
-- Therefore we morally use a representation closer to
--
-- @
-- data 'Wk' ctx ctx' where
--     'IdWk'   :: Wk ctx ctx
--     'KeepWk' :: Wk ctx ctx' -> Wk (S ctx)  (S ctx')
--     'SkipWk' :: Wk ctx ctx' -> Wk    ctx   (S ctx')
-- @
--
-- But we keep an invariant that identity weakenings are always represented by 'IdWk'.
--
-- >>> KeepWk IdWk
-- IdWk
--
-- And 'KeepWk' pattern doesn't match on identity weakenings.
--
-- >>> case IdWk :: Wk Ctx2 Ctx2 of { KeepWk _ -> "keep"; SkipWk _ -> "skip"; IdWk -> "id" } :: String
-- "id"
--
type Wk :: Ctx -> Ctx -> Type
type role Wk nominal nominal
data Wk ctx ctx' where
    IdWk :: Wk ctx ctx
    NeWk :: Wk1 ctx ctx' -> Wk ctx ctx'

type Wk1 :: Ctx -> Ctx -> Type
data Wk1 ctx ctx' where
    Wk1     ::                 Wk1    ctx   (S ctx)
    KeepWk1 :: Wk1 ctx ctx' -> Wk1 (S ctx)  (S ctx')
    SkipWk1 :: Wk1 ctx ctx' -> Wk1    ctx   (S ctx')

deriving instance Eq (Wk ctx ctx')
deriving instance Eq (Wk1 ctx ctx')

-- | Keep variable.
keepWk :: Wk ctx ctx' -> Wk (S ctx) (S ctx')
keepWk IdWk     = IdWk
keepWk (NeWk w) = NeWk (KeepWk1 w)

-- | Skip variable.
skipWk :: Wk ctx ctx' -> Wk ctx (S ctx')
skipWk IdWk     = wk1
skipWk (NeWk w) = NeWk (SkipWk1 w)

viewWk :: Wk ctx ctx' -> ViewWk ctx ctx'
viewWk IdWk               = IdWk'
viewWk (NeWk Wk1)         = SkipWk' IdWk
viewWk (NeWk (SkipWk1 w)) = SkipWk' (NeWk w)
viewWk (NeWk (KeepWk1 w)) = KeepWk' (NeWk w)

type ViewWk :: Ctx -> Ctx -> Type
data ViewWk ctx ctx' where
    IdWk'   :: ViewWk ctx ctx
    SkipWk' :: Wk ctx ctx' -> ViewWk    ctx  (S ctx')
    KeepWk' :: Wk ctx ctx' -> ViewWk (S ctx) (S ctx')

pattern KeepWk :: () => (a ~ S a', b ~ S b') => Wk a' b' -> Wk a b
pattern KeepWk w <- (viewWk -> KeepWk' w)
  where KeepWk w = keepWk w

pattern SkipWk :: () => (b ~ S b') => Wk a b' -> Wk a b
pattern SkipWk w <- (viewWk -> SkipWk' w)
  where SkipWk w = skipWk w

{-# COMPLETE IdWk, SkipWk, KeepWk #-}

instance Show (Wk ctx ctx') where
    showsPrec _ IdWk       = showString "IdWk"
    showsPrec d (KeepWk w) = showParen (d > 10) $ showString "KeepWk " . showsPrec 11 w
    showsPrec d (SkipWk w) = showParen (d > 10) $ showString "SkipWk " . showsPrec 11 w

-- | Weaken by one. @'wk1' = 'SkipWk' 'IdWk'@.
wk1 :: Wk ctx (S ctx)
wk1 = NeWk Wk1

-- | Weakening composition.
compWk :: Wk a b -> Wk b c -> Wk a c
compWk IdWk     w'        = w'
compWk (NeWk w) IdWk      = NeWk w
compWk (NeWk w) (NeWk w') = NeWk (compWk1 w w')

compWk1 :: Wk1  a b -> Wk1 b c -> Wk1 a c
compWk1 w           Wk1          = SkipWk1 w
compWk1 w           (SkipWk1 w') = SkipWk1 (compWk1 w w')
compWk1 Wk1         (KeepWk1 w') = SkipWk1 w'
compWk1 (SkipWk1 w) (KeepWk1 w') = SkipWk1 (compWk1 w w')
compWk1 (KeepWk1 w) (KeepWk1 w') = KeepWk1 (compWk1 w w')

-- | Weaken 'Idx', i.e. map index from smaller to larger context.
weakenIdx :: Wk ctx ctx' -> Idx ctx -> Idx ctx'
weakenIdx IdWk     x = x
weakenIdx (NeWk w) x = weaken1Idx w x

weaken1Idx :: Wk1 ctx ctx' -> Idx ctx -> Idx ctx'
weaken1Idx Wk1         x      = IS x
weaken1Idx (SkipWk1 w) x      = IS (weaken1Idx w x)
weaken1Idx (KeepWk1 _) IZ     = IZ
weaken1Idx (KeepWk1 w) (IS x) = IS (weaken1Idx w x)

-- | Weaken 'Size'.
weakenSize :: Wk ctx ctx' -> Size ctx -> Size ctx'
weakenSize IdWk     x = x
weakenSize (NeWk w) x = weaken1Size w x

weaken1Size :: Wk1 ctx ctx' -> Size ctx -> Size ctx'
weaken1Size Wk1         x      = SS x
weaken1Size (SkipWk1 w) x      = SS (weaken1Size w x)
weaken1Size (KeepWk1 w) (SS x) = SS (weaken1Size w x)

contractSize :: Wk ctx ctx' -> Size ctx' -> Size ctx
contractSize IdWk     x = x
contractSize (NeWk w) x = contract1Size w x

contract1Size :: Wk1 ctx ctx' -> Size ctx' -> Size ctx
contract1Size Wk1         (SS x) = x
contract1Size (SkipWk1 w) (SS x) = contract1Size w x
contract1Size (KeepWk1 w) (SS x) = SS (contract1Size w x)

-- | Contract 'Env' i.e. drop elements from larger context.
--
-- This function explains the 'KeepWk' and 'SkipWk' constructor names:
--
-- >>> weakenEnv (IdWk & SkipWk & KeepWk) (EmptyEnv :> 'a' :> 'b' :> 'c' :> 'd' :> 'e')
-- EmptyEnv :> 'a' :> 'b' :> 'c' :> 'e'
--
weakenEnv :: Wk ctx ctx' -> Env ctx' a -> Env ctx a
weakenEnv IdWk     xs = xs
weakenEnv (NeWk w) xs = weaken1Env w xs

weaken1Env :: Wk1 ctx ctx' -> Env ctx' a -> Env ctx a
weaken1Env Wk1         (xs :> _) = xs
weaken1Env (SkipWk1 w) (xs :> _) = weaken1Env w xs
weaken1Env (KeepWk1 w) (xs :> x) = weaken1Env w xs :> x

-- | 'setWeakenEnv' and 'weakenEnv' together form a lens.
--
-- >>> setWeakenEnv (IdWk & SkipWk & KeepWk) (EmptyEnv :> 'a' :> 'b') (EmptyEnv :> 'x' :> 'y' :> 'z')
-- EmptyEnv :> 'a' :> 'y' :> 'b'
--
setWeakenEnv :: Wk ctx ctx' -> Env ctx a -> Env ctx' a -> Env ctx' a
setWeakenEnv IdWk     env _    = env
setWeakenEnv (NeWk w) env env' = setWeaken1Env w env env'

-- | Setter made from 'setWeakenEnv' and 'weakenEnv'.
--
-- >>> overWeakenEnv (IdWk & SkipWk & KeepWk) (fmap toUpper) (EmptyEnv :> 'a' :> 'x' :> 'y' :> 'z')
-- EmptyEnv :> 'A' :> 'X' :> 'y' :> 'Z'
--
overWeakenEnv :: Wk ctx ctx' -> (Env ctx a -> Env ctx a) -> Env ctx' a -> Env ctx' a
overWeakenEnv w f env = setWeakenEnv w (f (weakenEnv w env)) env

setWeaken1Env :: Wk1 ctx ctx' -> Env ctx a -> Env ctx' a -> Env ctx' a
setWeaken1Env Wk1         xs        (_ :> y)  = xs :> y
setWeaken1Env (SkipWk1 w) xs        (ys :> y) = setWeaken1Env w xs ys :> y
setWeaken1Env (KeepWk1 w) (xs :> x) (ys :> _) = setWeaken1Env w xs ys :> x
