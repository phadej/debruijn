module PoriTT.Builtins (
    evalDescGlobal,
    allTypeGlobal,
    allTermGlobal,
) where

import qualified Data.Set as Set

import PoriTT.Base
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Name
import PoriTT.Nice
import PoriTT.Term

-- $setup
-- >>> import PoriTT.Info

mkGlobal :: Name -> Term EmptyCtx -> Term EmptyCtx -> Global
mkGlobal name tm ty = Global
    { gblName   = name
    , gblTerm   = Ann tm ty
    , gblType   = ty'
    , gblVal    = vann tm' ty'
    , gblInline = False
    }
  where
    tm' = evalTerm SZ EmptyEnv tm
    ty' = evalTerm SZ EmptyEnv ty

-------------------------------------------------------------------------------
-- evalDesc
-------------------------------------------------------------------------------

-- | Evaluate description: @evalDesc@
--
-- >>> infoGlobal evalDescGlobal
-- defined evalDesc
--   : Desc -> U -> U
--   = \ d X ->
--       indDesc
--         d
--         (\ _ -> U)
--         {:tt}
--         (\ S D F -> exists (s : S) * F s)
--         (\ D F -> X * F)
--
evalDescGlobal :: Global
evalDescGlobal = mkGlobal "evalDesc" evalDescTerm evalDescType

evalDescType :: Term ctx
evalDescType = Pie "_" Dsc $ Pie "_" Uni Uni

evalDescTerm :: Term ctx
evalDescTerm = Lam "d" $ Lam "X" $ Emb $ DeI
    (Var I1)
    (Lam "_" Uni)
    (Fin (Set.singleton "tt"))
    (Lam "S" $ Lam "D" $ Lam "F" $ Sgm "s" (Emb (Var I2)) (Emb (App (Var I1) (Emb (Var IZ)))))
    (Lam "D" $ Lam "F" $ Sgm "_" (Emb (Var I2)) (Emb (Var I1)))

-------------------------------------------------------------------------------
-- All
-------------------------------------------------------------------------------

{- |

>>> infoGlobal allTypeGlobal
defined All
  : forall (D : Desc) (X : U) -> (X -> U) -> evalDesc D X -> U
  = \ D' X P ->
      indDesc
        D'
        (\ D -> evalDesc D X -> U)
        (\ xs -> {:tt})
        (\ S D Dm xs -> Dm (xs .fst) (xs .snd))
        (\ D Dm xs -> P (xs .fst) * Dm (xs .snd))

-}
allTypeGlobal :: Global
allTypeGlobal = mkGlobal "All" allTypeTerm allTypeType

allTypeType :: Term ctx
allTypeType = Pie "D" Dsc $ Pie "X" Uni $ Pie "P" (Pie "_" (Emb (Var IZ)) Uni) $
    Pie "xs" (Gbl evalDescGlobal @@ var I2 @@ var I1) Uni

allTypeTerm :: Term ctx
allTypeTerm =
    Lam "D'" $ Lam "X" $ Lam "P" $ Emb $ DeI
        (var I2)
        (Lam "D" $ Pie "xs" (Gbl evalDescGlobal @@ var IZ @@ var I2) Uni)
        (Lam "xs" $ Fin (Set.singleton "tt"))
        (Lam "S" $ Lam "D" $ Lam "Dm" $ Lam "xs" $ var I1 @@ (var IZ .: "fst") @@ (var IZ .: "snd"))
        (Lam "D" $ Lam "Dm" $ Lam "xs" $ var I3 @@ (var IZ .: "fst") *** var I1 @@ (var IZ .: "snd"))

-------------------------------------------------------------------------------
-- all
-------------------------------------------------------------------------------

{- |

>>> infoGlobal allTermGlobal
defined all
  : forall
      (D : Desc) (X : U) (P : X -> U) ->
      (forall (x : X) -> P x) -> forall (xs : evalDesc D X) -> All D X P xs
  = \ D' X P p ->
      indDesc
        D'
        (\ D -> forall (xs : evalDesc D X) -> All D X P xs)
        (\ xs -> :tt)
        (\ S D allD xs -> allD (xs .fst) (xs .snd))
        (\ D allD xs -> p (xs .fst) , allD (xs .snd))

-}
allTermGlobal :: Global
allTermGlobal = mkGlobal "all" allTermTerm allTermType

allTermType :: Term ctx
allTermType =
  Pie "D" Dsc $
  Pie "X" Uni $
  Pie "P" (var IZ ~~> Uni) $
  Pie "p" (Pie "x" (var I1) $ var I1 @@ var IZ) $
  Pie "xs" (Gbl evalDescGlobal @@ var I3 @@ var I2) $
  Gbl allTypeGlobal @@ var I4 @@ var I3 @@ var I2 @@ var IZ

allTermTerm :: Term ctx
allTermTerm = Lam "D'" $ Lam "X" $ Lam "P" $ Lam "p" $ Emb $ DeI (var I3)
    (Lam "D" $ Pie "xs" (Gbl evalDescGlobal @@ var IZ @@ var I3) $
      Gbl allTypeGlobal @@ var I1 @@ var I4 @@ var I3 @@ var IZ)
    (Lam "xs" $ Lbl "tt")
    (Lam "S" $ Lam "D" $ Lam "allD" $ Lam "xs" $ var I1 @@ (var IZ .: "fst") @@ (var IZ .: "snd"))
    (Lam "D" $ Lam "allD" $ Lam "xs" $ Mul (var I3 @@ (var IZ .: "fst")) (var I1 @@ (var IZ .: "snd")))
