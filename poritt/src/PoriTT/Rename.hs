module PoriTT.Rename (
    resolve,
    RenameCtx,
    emptyRenameCtx,
    bindRenameCtx,
) where

import PoriTT.Raw
import PoriTT.Well

import qualified Data.Map.Strict as Map

import PoriTT.Base
import PoriTT.Global
import PoriTT.Loc
import PoriTT.Macro
import PoriTT.Name
import PoriTT.PP

-------------------------------------------------------------------------------
-- Name resolution context
-------------------------------------------------------------------------------

data RenameCtx ctx = RenameCtx
    { vars    :: !(Map Name (Idx ctx))
    , globals :: !(Map Name Global)
    , macros  :: !(Map Name Macro)
    , loc     :: !Loc
    }

emptyRenameCtx :: Map Name Global -> Map Name Macro -> RenameCtx EmptyCtx
emptyRenameCtx g m = RenameCtx Map.empty g m (startLoc "<unknown>")

bindRenameCtx
    :: RenameCtx ctx
    -> Maybe Name                -- ^ variable name
    -> RenameCtx (S ctx)
bindRenameCtx (RenameCtx xs g m l) x = RenameCtx
    { vars    = case x of
        Nothing -> fmap IS xs
        Just x' -> Map.insert x' IZ (fmap IS xs)
    , globals = g
    , macros  = m
    , loc     = l
    }

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

-- | So we can report all name resolution errors at once
newtype Validate a = V (Either (NonEmpty String) a)
  deriving Functor

instance Applicative Validate where
    pure = V . pure

    liftA2 f (V (Right x)) (V (Right y)) = V (Right (f x y))
    liftA2 _ (V (Left x))  (V (Right _)) = V (Left x)
    liftA2 _ (V (Right _)) (V (Left y))  = V (Left y)
    liftA2 _ (V (Left x))  (V (Left y))  = V (Left (x <> y))

validateBind :: Validate a -> (a -> Validate b) -> Validate b
validateBind (V (Left e))  _ = V (Left e)
validateBind (V (Right x)) k = k x

renameError :: RenameCtx ctx -> Doc -> [Doc] -> Validate a
renameError ctx msg extras = V $ Left $ pure $ ppRender False $ ppHanging
    (prettyLoc (loc ctx) <> ":" <+> msg)
    [ "*" <+> e
    | e <- extras
    ]

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

resolve
    :: RenameCtx ctx                         -- ^ Renaming context
    -> Raw                                   -- ^ Raw term
    -> Either (NonEmpty String) (Well ctx)   -- ^ Elaborated term
resolve ctx r = coerce (resolve' ctx r)

resolve'
    :: RenameCtx ctx              -- ^ Renaming context
    -> Raw                        -- ^ Raw term
    -> Validate (Well ctx)        -- ^ Renamed term
resolve' ctx (RVar n)
    | Just i <- Map.lookup n (vars ctx)
    = pure (WVar i)
resolve' ctx (RVar n)
    | Just g <- Map.lookup n (globals ctx)
    = pure (WGbl g)
resolve' ctx (RVar n)
    | Just (Macro _ ns w) <- Map.lookup n (macros ctx)
    = expandMacro ctx ns [] $ \ws cs ->
      pure $ wApps (subst (MkSub ws) w) cs
resolve' _   (RGbl g)
    = pure (WGbl g)
resolve' ctx (RVar n)   =
    renameError ctx
    ("Variable not in scope" <+> prettyName n)
    [ -- TODO: look for names in scope
    ]
resolve' ctx (RLoc l t) =
    WLoc l <$> resolve' ctx { loc = l } t
resolve' ctx (RLam x t) = do
    let ctx' = bindRenameCtx ctx (if x == holeName then Nothing else Just x)
    WLam x <$> resolve' ctx' t
resolve' ctx (RPie x a b) = do
    let ctx' = bindRenameCtx ctx (if x == holeName then Nothing else Just x)
    WPie x <$> resolve' ctx a <*> resolve' ctx' b
resolve' ctx (RSgm x a b) = do
    let ctx' = bindRenameCtx ctx (if x == holeName then Nothing else Just x)
    WSgm x <$> resolve' ctx a <*> resolve' ctx' b
resolve' ctx (RArr a b) = do
    let wArr a' b' = WPie holeName a' (weaken wk1 b')
    wArr <$> resolve' ctx a <*> resolve' ctx b
resolve' ctx (RPrd a b) = do
    let wPrd a' b' = WSgm holeName a' (weaken wk1 b')
    wPrd <$> resolve' ctx a <*> resolve' ctx b
resolve' ctx (RApp (unRLoc -> RVar a) bs)
    | Just (Macro _ ns w) <- Map.lookup a (macros ctx)
    = validateBind (traverse (traverse (resolve' ctx)) bs) $ \bs' ->
      expandMacro ctx ns bs' $ \ws cs ->
      pure $ wApps (subst (MkSub ws) w) cs
resolve' ctx (RApp a bs) = do
    wApps <$> resolve' ctx a <*> traverse (traverse (resolve' ctx)) bs
resolve' ctx (RAnn t s) =
    WAnn <$> resolve' ctx t <*> resolve' ctx s
resolve' ctx (RLet x t s) = do
    let ctx' = bindRenameCtx ctx (Just x)
    WLet x <$> resolve' ctx t <*> resolve' ctx' s
resolve' ctx (RMul t s) =
    WMul <$> resolve' ctx t <*> resolve' ctx s
resolve' ctx (RSwh e m ts) =
    WSwh <$> resolve' ctx e <*> resolve' ctx m <*> traverse (resolve' ctx) ts
resolve' ctx (RDeS t s) =
    WDeS <$> resolve' ctx t <*> resolve' ctx s
resolve' ctx (RDeX t) =
    WDeX <$> resolve' ctx t
resolve' ctx (RDeI e m x y z) =
    WDeI <$> resolve' ctx e <*> resolve' ctx m <*> resolve' ctx x <*> resolve' ctx y <*> resolve' ctx z
resolve' ctx (RMuu d) =
    WMuu <$> resolve' ctx d
resolve' ctx (RCon t) =
    WCon <$> resolve' ctx t
resolve' ctx (RInd e m c) =
    WInd <$> resolve' ctx e <*> resolve' ctx m <*> resolve' ctx c
resolve' ctx (RCod a) =
    WCod <$> resolve' ctx a
resolve' ctx (RQuo a) =
    WQuo <$> resolve' ctx a
resolve' ctx (RSpl a) =
    WSpl <$> resolve' ctx a
resolve' _   RHol = pure WHol
resolve' _   RUni = pure WUni
resolve' _   RDsc = pure WDsc
resolve' _   RDe1 = pure WDe1
resolve' _   (RLbl l) = pure (WLbl l)
resolve' _   (RFin ls) = pure (WFin ls)


expandMacro
    :: forall arity ctx r. RenameCtx ctx
    -> Env arity Name                -- ^ macro argument names
    -> [Either Selector (Well ctx)]  -- ^ apply arguments
    -> (Env arity (Well ctx) -> [Either Selector (Well ctx)] -> Validate r) -- ^ continuation with arguments and rest parameters
    -> Validate r
expandMacro ctx ns ts kont = go (rzeroAdd (sizeEnv ns)) EmptyEnv ts where
    go :: Add n m arity -> Env m (Well ctx) -> [Either Selector (Well ctx)] -> Validate r
    go AZ     ss rest             = kont ss rest
    go (AS a) ss (Right s : rest) = go (rsuccAdd a) (ss :> s) rest
    go (AS _) _  (Left s : _)     = renameError ctx ("Selector " <+> prettySelector s <+> "given as macro argument") []
    go (AS _) _  []               = renameError ctx "Not enough macro arguments" []

wApps :: Well ctx -> [Either Selector (Well ctx)] -> Well ctx
wApps f ts = foldl' (\f' t -> either (WSel f') (WApp f') t) f ts
