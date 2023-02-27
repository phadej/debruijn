-- | Used (in type-checking) terms
module PoriTT.Used (
    -- * Label induction: switch
    switchMotive,
    switchMotiveT,
    -- * Description induction
    descIndMotive,
    descIndMotive1,
    descIndMotiveS,
    descIndMotiveX,
    -- * Fixed point induction
    muMotiveT,
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.Nice
import PoriTT.Term

import {-# SOURCE #-} PoriTT.Builtins (allTypeGlobal, evalDescGlobal)

-- $setup
-- >>> import PoriTT.Base
-- >>> import PoriTT.Name
-- >>> import PoriTT.Term
-- >>> import qualified Data.Set as Set
-- >>> :set -XOverloadedStrings
--
-- >>> let pp env t = prettyTerm emptyNameScope env 0 t

-------------------------------------------------------------------------------
-- Switch motive
-------------------------------------------------------------------------------

-- | switch motive
--
--
switchMotive :: Set Label -> Term ctx
switchMotive ls = Fin ls ~~> Uni

switchMotiveT :: Label -> Term (S ctx)
switchMotiveT l = var IZ @@ Lbl l

-------------------------------------------------------------------------------
-- Description induction
-------------------------------------------------------------------------------

-- | indDesc motive
--
-- >>> pp EmptyEnv descIndMotive
-- Desc -> U
--
descIndMotive :: Term ctx
descIndMotive = Dsc ~~> Uni

-- |
--
-- >>>  pp (EmptyEnv :> "M") descIndMotive1
-- M `1
--
descIndMotive1 :: Term (S ctx)
descIndMotive1 = var IZ @@ De1

-- |
--
-- >>>  pp (EmptyEnv :> "M") descIndMotiveS
-- forall (S : U) (D : S -> Desc) -> (forall (s : S) -> M (D s)) -> M (`S S D)
--
descIndMotiveS :: Term (S ctx)
descIndMotiveS =
    Pie "S"   Uni $
    Pie "D"   (var IZ ~~> Dsc) $
    Pie "MDs" (Pie "s" (var I1) (var I3 @@ (var I1 @@ var IZ))) -- Γ := M S D; Γ := M S D s
              (var I3 @@ DeS (var I2) (var I1))                 -- Γ := M S D MDs

-- |
--
-- >>>  pp (EmptyEnv :> "M") descIndMotiveX
-- forall (D : Desc) -> M D -> M (`X D)
--
descIndMotiveX :: Term (S ctx)
descIndMotiveX =
    Pie "D"  Dsc $
    Pie "MD" (var I1 @@ var IZ) $
    var I2 @@ DeX (var I1)

-------------------------------------------------------------------------------
-- Fixed point induction
-------------------------------------------------------------------------------

-- |
--
-- >>> pp (EmptyEnv :> "D" :> "M") muMotiveT
-- forall (d : evalDesc D (mu D)) -> All D (mu D) M d -> M (con d)
--
muMotiveT :: Term (S (S ctx))
muMotiveT =
    Pie "d" (Gbl evalDescGlobal @@ var I1 @@ Muu (var I1)) $
    (Gbl allTypeGlobal @@ var I2 @@ Muu (var I2) @@ var I1 @@ var IZ) ~~>
    (var I1 @@ Con (var IZ))
