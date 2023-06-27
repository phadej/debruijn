-- | Quote from values ('VTerm' and 'VElim') to terms ('Term' and 'Elim').
--
-- We could quote to normal forms too (see "PoriTT.Norm"),
-- but in practice it's more convenient to quote into terms.
module PoriTT.Quote (
    quoteTerm,
    quoteElim,
    Unfold (..),
    prettyVElim,
    prettyVTerm,
    nfTerm,
    nfElim,
    preElim,
) where

import PoriTT.Base
import PoriTT.Eval
import PoriTT.Name
import PoriTT.PP
import PoriTT.Term
import PoriTT.Value

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
    -> Size ctx -> VTerm ctx -> Either EvalError (Term ctx)
quoteTerm u s (VLam x clos) = Lam x <$> quoteTerm u (SS s) (runZ s clos)
quoteTerm u s (VPie x a b)  = Pie x <$> quoteTerm u s a <*> quoteTerm u (SS s) (runZ s b)
quoteTerm u s (VSgm x a b)  = Sgm x <$> quoteTerm u s a <*> quoteTerm u (SS s) (runZ s b)
quoteTerm u s (VMul t r)    = Mul <$> quoteTerm u s t <*> quoteTerm u s r
quoteTerm u s (VDeS t r)    = DeS <$> quoteTerm u s t <*> quoteTerm u s r
quoteTerm u s (VDeX t)      = DeX <$> quoteTerm u s t
quoteTerm u s (VMuu t)      = Muu <$> quoteTerm u s t
quoteTerm u s (VCon t)      = Con <$> quoteTerm u s t
quoteTerm _ _ VUni          = pure Uni
quoteTerm _ _ VDsc          = pure Dsc
quoteTerm _ _ VDe1          = pure De1
quoteTerm _ _ (VLbl l)      = pure (Lbl l)
quoteTerm _ _ (VFin ls)     = pure (Fin ls)
quoteTerm u s (VCod t)      = Cod <$> quoteTerm u s t
quoteTerm _ s (VQuo t _)    = Quo <$> quoteSTerm NZ s t
quoteTerm u s (VEmb e)      = emb <$> quoteElim u s e

quoteElim :: Unfold -> Size ctx -> VElim ctx -> Either EvalError (Elim ctx)
quoteElim u s (VNeu l sp)   = quoteSpine (unfoldSp u) s (pure (Var (lvlToIdx s l))) sp
quoteElim u s (VGbl g sp t) = case u of
    UnfoldAll  -> quoteElim u s t
    UnfoldElim -> quoteElim u s t
    UnfoldNone -> quoteSpine u s (pure (Gbl g)) sp
quoteElim u s (VAnn t a)    = ann <$> quoteTerm u s t <*> quoteTerm u s a
quoteElim _ _ (VErr msg)    = Left msg

unfoldSp :: Unfold -> Unfold
unfoldSp UnfoldElim = UnfoldNone
unfoldSp u          = u

quoteSpine :: Unfold -> Size ctx -> Either EvalError (Elim ctx) -> Spine ctx -> Either EvalError (Elim ctx)
quoteSpine _ _ h VNil              = h
quoteSpine u s h (VApp sp e)       = App <$> quoteSpine u s h sp <*> quoteTerm u s e
quoteSpine u s h (VSel sp z)       = Sel <$> quoteSpine u s h sp <*> pure z
quoteSpine u s h (VSwh sp m ts)    = Swh <$> quoteSpine u s h sp <*> quoteTerm u s m <*> traverse (quoteTerm u s) ts
quoteSpine u s h (VDeI sp m x y z) = DeI <$> quoteSpine u s h sp <*> quoteTerm u s m <*> quoteTerm u s x <*> quoteTerm u s y <*> quoteTerm u s z
quoteSpine u s h (VInd sp m t)     = Ind <$> quoteSpine u s h sp <*> quoteTerm u s m <*> quoteTerm u s t
quoteSpine u s h (VSpl sp)         = Spl <$> quoteSpine u s h sp

-------------------------------------------------------------------------------
-- Quoting of STerm and SElim
-------------------------------------------------------------------------------

quoteSTerm :: Natural -> Size ctx -> STerm ctx -> Either EvalError (Term ctx)
quoteSTerm l      s (SLam n clos) = Lam n <$> quoteSTerm l (SS s) (runSTZ l s clos)
quoteSTerm l      s (SPie x a b)  = Pie x <$> quoteSTerm l s a <*> quoteSTerm l (SS s) (runSTZ l s b)
quoteSTerm l      s (SSgm x a b)  = Sgm x <$> quoteSTerm l s a <*> quoteSTerm l (SS s) (runSTZ l s b)
quoteSTerm l      s (SMul t r)    = Mul <$> quoteSTerm l s t <*> quoteSTerm l s r
quoteSTerm _      _ SUni          = pure Uni
quoteSTerm _      _ SDsc          = pure Dsc
quoteSTerm _      _ SDe1          = pure De1
quoteSTerm l      s (SDeS t r)    = DeS <$> quoteSTerm l s t <*> quoteSTerm l s r
quoteSTerm l      s (SDeX t)      = DeX <$> quoteSTerm l s t
quoteSTerm _      _ (SLbl l)      = pure (Lbl l)
quoteSTerm _      _ (SFin ls)     = pure (Fin ls)
quoteSTerm l      s (SMuu t)      = Muu <$> quoteSTerm l s t
quoteSTerm l      s (SCon t)      = Con <$> quoteSTerm l s t
quoteSTerm l      s (SCod t)      = Cod <$> quoteSTerm l s t
quoteSTerm l      s (SQuo t)      = Quo <$> quoteSTerm (NS l) s t
quoteSTerm l      s (SEmb e)      = Emb <$> quoteSElim l s e
quoteSTerm NZ     s (SVal t)      = quoteTerm UnfoldNone s t
quoteSTerm (NS _) _ (SVal _)      = Left EvalErrorStg

quoteSElim :: Natural -> Size ctx -> SElim ctx -> Either EvalError (Elim ctx)
quoteSElim _      s (SVar x)         = pure $ Var (lvlToIdx s x)
quoteSElim _      _ (SGbl g)         = pure $ Gbl g
quoteSElim l      s (SApp f t)       = App <$> quoteSElim l s f <*> quoteSTerm l s t
quoteSElim l      s (SSel e t)       = Sel <$> quoteSElim l s e <*> pure t
quoteSElim l      s (SSwh e m ts)    = Swh <$> quoteSElim l s e <*> quoteSTerm l s m <*> traverse (quoteSTerm l s) ts
quoteSElim l      s (SInd e m t)     = Ind <$> quoteSElim l s e <*> quoteSTerm l s m <*> quoteSTerm l s t
quoteSElim l      s (SDeI e m x y z) = DeI <$> quoteSElim l s e <*> quoteSTerm l s m <*> quoteSTerm l s x <*> quoteSTerm l s y <*> quoteSTerm l s z
quoteSElim l      s (SAnn t a)       = Ann <$> quoteSTerm l s t <*> quoteSTerm l s a
quoteSElim (NS l) s (SSpl e)         = Spl <$> quoteSElim l s e
quoteSElim NZ     _ (SSpl _)         = Left EvalErrorStg -- shouldn't be top-level splices anymore
quoteSElim l      s (SLet x e f)     = Let x <$> quoteSElim l s e <*> quoteSElim l (SS s) (runSEZ l s f)
quoteSElim _      _ (SErr msg)       = Left msg

-------------------------------------------------------------------------------
-- Normalisation
-------------------------------------------------------------------------------

nfTerm :: Unfold  -> Size ctx' -> EvalEnv ctx ctx' -> Term ctx -> Either EvalError (Term ctx')
nfTerm u s ee t = quoteTerm u s (evalTerm s ee t)

nfElim :: Unfold  -> Size ctx' -> EvalEnv ctx ctx' -> Elim ctx -> Either EvalError (Elim ctx')
nfElim u s ee t = quoteElim u s (evalElim s ee t)

-------------------------------------------------------------------------------
-- Staging
-------------------------------------------------------------------------------

preElim :: Size ctx' -> EvalEnv' ctx ctx' -> Elim ctx -> Either EvalError (Elim ctx')
preElim s env e = quoteSElim NZ s (stageElim NZ s env e)

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyVTerm :: Size ctx -> NameScope -> Env ctx Name -> VTerm ctx -> Doc
prettyVTerm s ns env v = case quoteTerm UnfoldNone s v of
    Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyTerm ns env 0 n

prettyVElim :: Size ctx -> NameScope -> Env ctx Name -> VElim ctx -> Doc
prettyVElim s ns env v = case quoteElim UnfoldNone s v of
    Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
    Right e  -> prettyElim ns env 0 e
