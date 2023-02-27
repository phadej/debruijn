module PoriTT.Well (
    Well (..),
    prettyWell,
) where

import PoriTT.Base
import PoriTT.Global
import PoriTT.Loc
import PoriTT.Name
import PoriTT.PP
import PoriTT.Raw

-- | Well scoped terms.
type Well :: Ctx -> Type
data Well ctx where
    WLam :: Name -> Well (S ctx) -> Well ctx
    WPie :: Name -> Well ctx -> Well (S ctx) -> Well ctx
    WSgm :: Name -> Well ctx -> Well (S ctx) -> Well ctx
    WMul :: Well ctx -> Well ctx -> Well ctx
    WUni :: Well ctx
    WVar :: Idx ctx -> Well ctx
    WGbl :: Global -> Well ctx
    WApp :: Well ctx -> Well ctx -> Well ctx
    WSel :: Well ctx -> Selector -> Well ctx
    WSwh :: Well ctx -> Well ctx -> Map Label (Well ctx) -> Well ctx
    WAnn :: Well ctx -> Well ctx -> Well ctx
    WLet :: Name -> Well ctx -> Well (S ctx) -> Well ctx
    WLbl :: Label -> Well ctx
    WFin :: Set Label -> Well ctx
    WDsc :: Well ctx
    WDe1 :: Well ctx
    WDeS :: Well ctx -> Well ctx -> Well ctx
    WDeX :: Well ctx -> Well ctx
    WDeI :: Well ctx -> Well ctx -> Well ctx -> Well ctx -> Well ctx -> Well ctx
    WMuu :: Well ctx -> Well ctx
    WCon :: Well ctx -> Well ctx
    WInd :: Well ctx -> Well ctx -> Well ctx -> Well ctx
    WHol :: Well ctx
    WLoc :: Loc -> Well ctx -> Well ctx

deriving instance Show (Well ctx)

-------------------------------------------------------------------------------
-- Renaming
-------------------------------------------------------------------------------

instance Renamable Well where rename = defaultRename; weaken = defaultWeaken

instance RenamableA Well where
    grename r (WLam x t)       = WLam x <$> grename (keep r) t
    grename r (WPie x a b)     = WPie x <$> grename r a <*> grename (keep r) b
    grename r (WSgm x a b)     = WSgm x <$> grename r a <*> grename (keep r) b
    grename _ WUni             = pure WUni
    grename _ WHol             = pure WHol
    grename _ WDsc             = pure WDsc
    grename _ WDe1             = pure WDe1
    grename r (WDeS t s)       = WDeS <$> grename r t <*> grename r s
    grename r (WDeX t)         = WDeX <$> grename r t
    grename r (WDeI d m x y z) = WDeI <$> grename r d <*> grename r m <*> grename r x <*> grename r y <*> grename r z
    grename r (WVar i)         = WVar <$> grename r i
    grename _ (WGbl g)         = pure (WGbl g)
    grename _ (WLbl l)         = pure (WLbl l)
    grename _ (WFin ls)        = pure (WFin ls)
    grename r (WApp f t)       = WApp <$> grename r f <*> grename r t
    grename r (WSel e s)       = flip WSel s <$> grename r e
    grename r (WAnn t s)       = WAnn <$> grename r t <*> grename r s
    grename r (WSwh e m ts)    = WSwh <$> grename r e <*> grename r m <*> traverse (grename r) ts
    grename r (WLet x t s)     = WLet x <$> grename r t <*> grename (keep r) s
    grename r (WMul t s)       = WMul <$> grename r t <*> grename r s
    grename r (WMuu d)         = WMuu <$> grename r d
    grename r (WCon t)         = WCon <$> grename r t
    grename r (WInd e m c)     = WInd <$> grename r e <*> grename r m <*> grename r c
    grename r (WLoc l t)       = WLoc l <$> grename r t

-------------------------------------------------------------------------------
-- Subst
-------------------------------------------------------------------------------

instance Var Well where
    var = WVar

instance Subst Well where
    subst sub (WVar x)   = substIdx sub x
    subst sub (WApp f t) = WApp (subst sub f) (subst sub t)
    subst _   (WLbl l)   = WLbl l
    subst sub (WMul t s) = WMul (subst sub t) (subst sub s)
    subst sub (WCon t)   = WCon (subst sub t)
    subst sub (WLoc _ t) = subst sub t
    subst _  t = error $ show t

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyWell :: NameScope -> Env ctx Name -> Int -> Well ctx -> Doc
prettyWell ns env d x = prettyRaw d (toRaw ns env x)

instance ToRaw Well where
    toRaw ns env (WLam x t)
        = withFreshName ns x $ \ns' x' ->
          RLam x' (toRaw ns' (env :> x') t)
    toRaw ns env (WPie x a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (WSgm x a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        = RPrd (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RSgm x' (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (WLet x t s)
        = withFreshName ns x $ \ns' x' ->
          RLet x' (toRaw ns env t) (toRaw ns' (env :> x') s)

    toRaw ns env (WMul t s)       = RMul (toRaw ns env t) (toRaw ns env s)
    toRaw _  _   WUni             = RUni
    toRaw _  _   (WLbl l)         = RLbl l
    toRaw _  _   (WFin ls)        = RFin ls
    toRaw _  env (WVar i)         = RVar (lookupEnv i env)
    toRaw _  _   (WGbl g)         = RGbl g
    toRaw ns env (WApp f t)       = rapp (toRaw ns env f) (toRaw ns env t)
    toRaw ns env (WSel e s)       = rsel (toRaw ns env e) s
    toRaw ns env (WSwh e m ts)    = RSwh (toRaw ns env e) (toRaw ns env m) (fmap (toRaw ns env) ts)
    toRaw _  _   WHol             = RHol
    toRaw _  _   WDsc             = RDsc
    toRaw _  _   WDe1             = RDe1
    toRaw ns env (WDeS t s)       = RDeS (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WDeX t)         = RDeX (toRaw ns env t)
    toRaw ns env (WDeI e m x y z) = RDeI (toRaw ns env e) (toRaw ns env m) (toRaw ns env x) (toRaw ns env y) (toRaw ns env z)
    toRaw ns env (WMuu d)         = RMuu (toRaw ns env d)
    toRaw ns env (WCon t)         = RCon (toRaw ns env t)
    toRaw ns env (WInd e m c)     = RInd (toRaw ns env e) (toRaw ns env m) (toRaw ns env c)
    toRaw ns env (WAnn t s)       = RAnn (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WLoc _ t)       = toRaw ns env t
