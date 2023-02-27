-- | We can quote to normal terms.
--
-- Note: these are not correct normal forms.
-- We should have normal terms and normal elims
-- (and two neutral forms: beta-neutral and emb-neutral).
module PoriTT.Norm (
    quoteTerm,
    quoteElim,
    Unfold (..),
    prettyNf,
    prettyNe,
    prettyVTerm,
    prettyVElim,
    Nf,
    Ne,
) where

import PoriTT.Base
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Name
import PoriTT.PP
import PoriTT.Raw

-------------------------------------------------------------------------------
-- Normal forms
-------------------------------------------------------------------------------

type Nf :: Ctx -> Type
data Nf ctx where
    NLam :: Name -> Nf (S ctx) -> Nf ctx
    NPie :: Name -> Nf ctx -> Nf (S ctx) -> Nf ctx
    NSgm :: Name -> Nf ctx -> Nf (S ctx) -> Nf ctx
    NMul :: Nf ctx -> Nf ctx -> Nf ctx
    NUni :: Nf ctx
    NDsc :: Nf ctx
    NDe1 :: Nf ctx
    NDeS :: Nf ctx -> Nf ctx -> Nf ctx
    NDeX :: Nf ctx -> Nf ctx
    NMuu :: Nf ctx -> Nf ctx
    NCon :: Nf ctx -> Nf ctx
    NLbl :: Label -> Nf ctx
    NFin :: Set Label -> Nf ctx
    Neut :: Ne ctx -> Nf ctx

type Ne :: Ctx -> Type
data Ne ctx where
    NVar :: Idx ctx -> Ne ctx
    NGbl :: Global -> Ne ctx
    NApp :: Ne ctx -> Nf ctx -> Ne ctx
    NSel :: Ne ctx -> Selector -> Ne ctx
    NSwh :: Ne ctx -> Nf ctx -> Map Label (Nf ctx) -> Ne ctx
    NDeI :: Ne ctx -> Nf ctx -> Nf ctx -> Nf ctx -> Nf ctx -> Ne ctx
    NInd :: Ne ctx -> Nf ctx -> Nf ctx -> Ne ctx

deriving instance Show (Nf ctx)
deriving instance Show (Ne ctx)

-------------------------------------------------------------------------------
-- Quoting
-------------------------------------------------------------------------------

-- | How much to unfold when quoting?
data Unfold
    = UnfoldNone  -- ^ unfold nothing
    | UnfoldElim  -- ^ don't unfold spines of neutral elements
    | UnfoldAll   -- ^ unfold all
  deriving Show

-- | Quote semantic value into normal form.
--
-- Quoting will force the evaluation errors.
--
quoteTerm
    :: Unfold -- ^ Unfold global definitions
    -> Size ctx -> VTerm ctx -> Either EvalError (Nf ctx)
quoteTerm u s (VLam x clos) = NLam x <$> quoteTerm u (SS s) (runZ s clos)
quoteTerm u s (VPie x a b)  = NPie x <$> quoteTerm u s a <*> quoteTerm u (SS s) (runZ s b)
quoteTerm u s (VSgm x a b)  = NSgm x <$> quoteTerm u s a <*> quoteTerm u (SS s) (runZ s b)
quoteTerm u s (VMul t r)    = NMul <$> quoteTerm u s t <*> quoteTerm u s r
quoteTerm u s (VDeS t r)    = NDeS <$> quoteTerm u s t <*> quoteTerm u s r
quoteTerm u s (VDeX t)      = NDeX <$> quoteTerm u s t
quoteTerm u s (VMuu t)      = NMuu <$> quoteTerm u s t
quoteTerm u s (VCon t)      = NCon <$> quoteTerm u s t
quoteTerm _ _ VUni          = pure NUni
quoteTerm _ _ VDsc          = pure NDsc
quoteTerm _ _ VDe1          = pure NDe1
quoteTerm _ _ (VLbl l)      = pure (NLbl l)
quoteTerm _ _ (VFin ls)     = pure (NFin ls)
quoteTerm u s (VEmb e)      = quoteElim u s e

quoteElim :: Unfold -> Size ctx -> VElim ctx -> Either EvalError (Nf ctx)
quoteElim u s (VNeu l sp)   = Neut <$> quoteSpine (unfoldSp u) s (pure (NVar (lvlToIdx s l))) sp
quoteElim u s (VGbl g sp t) = case u of
    UnfoldAll  -> quoteElim u s t
    UnfoldElim -> quoteElim u s t
    UnfoldNone -> Neut <$> quoteSpine u s (pure (NGbl g)) sp
quoteElim u s (VAnn t _)    = quoteTerm u s t
quoteElim _ _ (VErr msg)    = Left msg

unfoldSp :: Unfold -> Unfold
unfoldSp UnfoldElim = UnfoldNone
unfoldSp u          = u

quoteSpine :: Unfold -> Size ctx -> Either EvalError (Ne ctx) -> Spine ctx -> Either EvalError (Ne ctx)
quoteSpine _ _ h VNil              = h
quoteSpine u s h (VApp sp e)       = NApp <$> quoteSpine u s h sp <*> quoteTerm u s e
quoteSpine u s h (VSel sp z)       = NSel <$> quoteSpine u s h sp <*> pure z
quoteSpine u s h (VSwh sp m ts)    = NSwh <$> quoteSpine u s h sp <*> quoteTerm u s m <*> traverse (quoteTerm u s) ts
quoteSpine u s h (VDeI sp m x y z) = NDeI <$> quoteSpine u s h sp <*> quoteTerm u s m <*> quoteTerm u s x <*> quoteTerm u s y <*> quoteTerm u s z
quoteSpine u s h (VInd sp m t)     = NInd <$> quoteSpine u s h sp <*> quoteTerm u s m <*> quoteTerm u s t

-------------------------------------------------------------------------------
-- Renaming
-------------------------------------------------------------------------------

instance Renamable Nf where rename = defaultRename; weaken = defaultWeaken
instance Renamable Ne where rename = defaultRename; weaken = defaultWeaken

instance RenamableA Nf where
    grename r (NLam x t)   = NLam x <$> grename (keep r) t
    grename r (NPie x a b) = NPie x <$> grename r a <*> grename (keep r) b
    grename r (NSgm x a b) = NSgm x <$> grename r a <*> grename (keep r) b
    grename r (NMul t s)   = NMul <$> grename r t <*> grename r s
    grename _ (NLbl l)     = pure (NLbl l)
    grename _ (NFin ls)    = pure (NFin ls)
    grename _ NUni         = pure NUni
    grename _ NDsc         = pure NDsc
    grename _ NDe1         = pure NDe1
    grename r (NDeS t s)   = NDeS <$> grename r t <*> grename r s
    grename r (NDeX t)     = NDeX <$> grename r t
    grename r (NMuu d)     = NMuu <$> grename r d
    grename r (NCon t)     = NCon <$> grename r t
    grename r (Neut t)     = Neut <$> grename r t

instance RenamableA Ne where
    grename r (NVar i)         = NVar <$> grename r i
    grename _ (NGbl g)         = pure (NGbl g)
    grename r (NApp f t)       = NApp <$> grename r f <*> grename r t
    grename r (NSel e s)       = flip NSel s <$> grename r e
    grename r (NSwh e m ts)    = NSwh <$> grename r e <*> grename r m <*> traverse (grename r) ts
    grename r (NDeI d m x y z) = NDeI <$> grename r d <*> grename r m <*> grename r x <*> grename r y <*> grename r z
    grename r (NInd e m t)     = NInd <$> grename r e <*> grename r m <*> grename r t

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyNf :: NameScope -> Env ctx Name -> Int -> Nf ctx -> Doc
prettyNf ns env d x = prettyRaw d (toRaw ns env x)

prettyNe :: NameScope -> Env ctx Name -> Int -> Ne ctx -> Doc
prettyNe ns env d x = prettyRaw d (toRaw ns env x)

prettyVTerm :: Size ctx -> NameScope -> Env ctx Name -> VTerm ctx -> Doc
prettyVTerm s ns env v = case quoteTerm UnfoldNone s v of
    Left err -> ppText (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyNf ns env 0 n

prettyVElim :: Size ctx -> NameScope -> Env ctx Name -> VElim ctx -> Doc
prettyVElim s ns env v = case quoteElim UnfoldNone s v of
    Left err -> ppText (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyNf ns env 0 n

instance ToRaw Nf where
    toRaw ns env (NLam x t)
        = withFreshName ns x $ \ns' x' ->
          RLam x' (toRaw ns' (env :> x') t)
    toRaw ns env (NPie x a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (NSgm x a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        = RPrd (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RSgm x' (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (NMul t s) = RMul (toRaw ns env t) (toRaw ns env s)
    toRaw _  _   NUni       = RUni
    toRaw _  _   NDsc       = RDsc
    toRaw _  _   NDe1       = RDe1
    toRaw ns env (NDeS t s) = RDeS (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (NDeX t)   = RDeX (toRaw ns env t)
    toRaw ns env (NMuu d)   = RMuu (toRaw ns env d)
    toRaw ns env (NCon t)   = RCon (toRaw ns env t)
    toRaw _  _   (NLbl l)   = RLbl l
    toRaw _  _   (NFin ls)  = RFin ls
    toRaw ns env (Neut e)   = toRaw ns env e

instance ToRaw Ne where
    toRaw _  env (NVar i)         = RVar (lookupEnv i env)
    toRaw _  _   (NGbl g)         = RGbl g
    toRaw ns env (NApp f t)       = rapp (toRaw ns env f) (toRaw ns env t)
    toRaw ns env (NSel e s)       = rsel (toRaw ns env e) s
    toRaw ns env (NSwh e m ts)    = RSwh (toRaw ns env e) (toRaw ns env m) (fmap (toRaw ns env) ts)
    toRaw ns env (NDeI e m x y z) = RDeI (toRaw ns env e) (toRaw ns env m) (toRaw ns env x) (toRaw ns env y) (toRaw ns env z)
    toRaw ns env (NInd e m c)     = RInd (toRaw ns env e) (toRaw ns env m) (toRaw ns env c)
