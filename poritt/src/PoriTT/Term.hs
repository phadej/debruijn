module PoriTT.Term (
    Term (..),
    Elim (..),
    prettyTerm,
    prettyElim,
    emb,
    ann,
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.PP
import PoriTT.Raw

import {-# SOURCE #-} PoriTT.Global (Global)

-- | Term types are checked
type Term :: Ctx -> Type
data Term ctx where
    Pie :: Name -> Term ctx -> Term (S ctx) -> Term ctx
    Lam :: Name -> Term (S ctx) -> Term ctx
    Mul :: Term ctx -> Term ctx -> Term ctx
    Sgm :: Name -> Term ctx -> Term (S ctx) -> Term ctx
    Lbl :: Label -> Term ctx
    Fin :: Set Label -> Term ctx
    Uni :: Term ctx
    Dsc :: Term ctx
    De1 :: Term ctx
    DeS :: Term ctx -> Term ctx -> Term ctx
    DeX :: Term ctx -> Term ctx
    Muu :: Term ctx -> Term ctx
    Con :: Term ctx -> Term ctx
    Cod :: Term ctx -> Term ctx
    Quo :: Term ctx -> Term ctx
    Emb :: Elim ctx -> Term ctx
    WkT :: Wk ctx ctx' -> Term ctx -> Term ctx'

-- | Elimination types are inferred
type Elim :: Ctx -> Type
data Elim ctx where
    Var :: Idx ctx -> Elim ctx
    Gbl :: Global -> Elim ctx
    App :: Elim ctx -> Term ctx -> Elim ctx
    Sel :: Elim ctx -> Selector -> Elim ctx
    Swh :: Elim ctx -> Term ctx -> Map Label (Term ctx) -> Elim ctx
    DeI :: Elim ctx -> Term ctx -> Term ctx -> Term ctx -> Term ctx -> Elim ctx
    Ind :: Elim ctx -> Term ctx -> Term ctx -> Elim ctx
    Spl :: Elim ctx -> Elim ctx
    Ann :: Term ctx -> Term ctx -> Elim ctx
    Let :: Name -> Elim ctx -> Elim (S ctx) -> Elim ctx
    WkE :: Wk ctx ctx' -> Elim ctx -> Elim ctx'

deriving instance Show (Term ctx)
deriving instance Show (Elim ctx)

-------------------------------------------------------------------------------
-- Smart constructors
-------------------------------------------------------------------------------

-- | We need to do this, as quoteElim may unfold global terms.
emb :: Elim ctx -> Term ctx
emb (Ann t _) = t
emb e         = Emb e

-- | This is slightly wrong to do so
-- but we do similar simplification in conversion
-- so doing it here is justified.
ann :: Term ctx -> Term ctx -> Elim ctx
ann (Emb e) _ = e
ann t       a = Ann t a

-------------------------------------------------------------------------------
-- Renaming
-------------------------------------------------------------------------------

instance Renamable Term where
    rename = defaultRename

    -- we have explicit weakening in the terms.
    -- it doesn't complicate evaluation nor linting,
    -- in these cases we don't end up traversing terms extra times.
    weaken w (WkT w' t) = WkT (compWk w' w) t
    weaken w t          = WkT w t

instance Renamable Elim where
    rename = defaultRename
    weaken w (WkE w' e) = WkE (compWk w' w) e
    weaken w (Var i)    = Var (weakenIdx w i)
    weaken _ (Gbl g)    = Gbl g
    weaken w e          = WkE w e

instance RenamableA Term where
    grename r (Lam x t)   = Lam x <$> grename (keep r) t
    grename r (Pie x a b) = Pie x <$> grename r a <*> grename (keep r) b
    grename r (Sgm x a b) = Sgm x <$> grename r a <*> grename (keep r) b
    grename _ Uni         = pure Uni
    grename _ Dsc         = pure Dsc
    grename _ De1         = pure De1
    grename r (DeS t s)   = DeS <$> grename r t <*> grename r s
    grename r (DeX t)     = DeX <$> grename r t
    grename r (Emb e)     = Emb <$> grename r e
    grename r (Mul t s)   = Mul <$> grename r t <*> grename r s
    grename _ (Lbl l)     = pure (Lbl l)
    grename _ (Fin ls)    = pure (Fin ls)
    grename r (Muu d)     = Muu <$> grename r d
    grename r (Con t)     = Con <$> grename r t
    grename r (Cod t)     = Cod <$> grename r t
    grename r (Quo t)     = Quo <$> grename r t
    grename r (WkT w t)   = grename (weakenIdxMapping w r) t

instance RenamableA Elim where
    grename r (Var i)         = Var <$> grename r i
    grename _ (Gbl g)         = pure (Gbl g)
    grename r (App f t)       = App <$> grename r f <*> grename r t
    grename r (Sel e s)       = flip Sel s <$> grename r e
    grename r (Ann t s)       = Ann <$> grename r t <*> grename r s
    grename r (Swh e m ts)    = Swh <$> grename r e <*> grename r m <*> traverse (grename r) ts
    grename r (DeI d m x y z) = DeI <$> grename r d <*> grename r m <*> grename r x <*> grename r y <*> grename r z
    grename r (Let x t s)     = Let x <$> grename r t <*> grename (keep r) s
    grename r (Ind e m c)     = Ind <$> grename r e <*> grename r m <*> grename r c
    grename r (Spl e)         = Spl <$> grename r e
    grename r (WkE w e)       = grename (weakenIdxMapping w r) e

-------------------------------------------------------------------------------
-- Var
-------------------------------------------------------------------------------

instance Var Elim where
    var = Var

instance Var Term where
    var = Emb . Var

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyTerm :: NameScope -> Env ctx Name -> Int -> Term ctx -> Doc
prettyTerm ns env d t = prettyRaw d (toRaw ns env t)

prettyElim :: NameScope -> Env ctx Name -> Int -> Elim ctx -> Doc
prettyElim ns env d e = prettyRaw d (toRaw ns env e)

instance ToRaw Term where
    toRaw ns env (Lam x t)
        = withFreshName ns x $ \ns' x' ->
          RLam x' (toRaw ns' (env :> x') t)

    toRaw ns env (Pie x a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (Sgm x a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        = RPrd (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RSgm x' (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (Mul t s) = RMul (toRaw ns env t) (toRaw ns env s)
    toRaw _  _   Uni       = RUni
    toRaw _  _   Dsc       = RDsc
    toRaw _  _   De1       = RDe1
    toRaw ns env (DeS t s) = RDeS (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (DeX t)   = RDeX (toRaw ns env t)
    toRaw ns env (Muu d)   = RMuu (toRaw ns env d)
    toRaw ns env (Con t)   = RCon (toRaw ns env t)
    toRaw ns env (Cod a)   = RCod (toRaw ns env a)
    toRaw ns env (Quo t)   = RQuo (toRaw ns env t)
    toRaw ns env (Emb e)   = toRaw ns env e
    toRaw _  _   (Lbl l)   = RLbl l
    toRaw _  _   (Fin ls)  = RFin ls
    toRaw ns env (WkT w t) = toRaw ns (weakenEnv w env) t

instance ToRaw Elim where
    toRaw ns env (Let x t s)
        = withFreshName ns x $ \ns' x' ->
          RLet x' (toRaw ns env t) (toRaw ns' (env :> x') s)

    toRaw ns env (Swh e m ts)    = RSwh (toRaw ns env e) (toRaw ns env m) (fmap (toRaw ns env) ts)
    toRaw _  env (Var i)         = RVar (lookupEnv i env)
    toRaw _  _   (Gbl g)         = RGbl g
    toRaw ns env (App f t)       = rapp (toRaw ns env f) (toRaw ns env t)
    toRaw ns env (Sel e s)       = rsel (toRaw ns env e) s
    toRaw ns env (DeI e m x y z) = RDeI (toRaw ns env e) (toRaw ns env m) (toRaw ns env x) (toRaw ns env y) (toRaw ns env z)
    toRaw ns env (Ind e m c)     = RInd (toRaw ns env e) (toRaw ns env m) (toRaw ns env c)
    toRaw ns env (Spl e)         = RSpl (toRaw ns env e)
    toRaw ns env (Ann t s)       = RAnn (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WkE w e)       = toRaw ns (weakenEnv w env) e
