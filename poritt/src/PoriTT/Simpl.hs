module PoriTT.Simpl (
    simplTerm,
    simplElim,
) where

import qualified Data.Map.Strict as Map

import PoriTT.Base
import PoriTT.Global
import PoriTT.Nice
import PoriTT.Term

simplTerm :: Size ctx' -> Sub Elim ctx ctx' -> Term ctx -> Term ctx'
simplTerm size sub (WkT w t)   = simplTerm size (weakenSub w sub) t
simplTerm size sub (Lam n t)   = Lam n (simplTerm (SS size) (keepSub sub) t)
simplTerm size sub (Pie n a b) = Pie n (simplTerm size sub a) (simplTerm (SS size) (keepSub sub) b)
simplTerm size sub (Sgm n a b) = Sgm n (simplTerm size sub a) (simplTerm (SS size) (keepSub sub) b)
simplTerm size sub (Mul t s)   = Mul (simplTerm size sub t) (simplTerm size sub s)
simplTerm _    _   (Lbl l)     = Lbl l
simplTerm _    _   (Fin ls)    = Fin ls
simplTerm _    _   Uni         = Uni
simplTerm _    _   Dsc         = Dsc
simplTerm _    _   De1         = De1
simplTerm size sub (DeS s t)   = DeS (simplTerm size sub s) (simplTerm size sub t)
simplTerm size sub (DeX t)     = DeX (simplTerm size sub t)
simplTerm size sub (Muu t)     = Muu (simplTerm size sub t)
simplTerm size sub (Con t)     = Con (simplTerm size sub t)
simplTerm size sub (Emb e)
    | Ann t _ <- e
    = simplTerm size sub t

    | otherwise
    = emb (simplElim size sub e)

simplElim :: Size ctx' -> Sub Elim ctx ctx' -> Elim ctx -> Elim ctx'
simplElim size sub (WkE w e) = simplElim size (weakenSub w sub) e
simplElim _    sub (Var i)   = substIdx sub i
simplElim size _   (Gbl g)
    | gblInline g       = weakenSize size (gblTerm g)
    | otherwise         = Gbl g
simplElim size sub (Let n t s)
    | shouldInline t
    = simplElim size (snocSub sub (simplElim size sub t)) s

    | otherwise
    = Let n (simplElim size sub t) (simplElim (SS size) (keepSub sub) s)

simplElim size sub (App f s)
    | Ann (Lam _ t) (Pie _ a b) <- f
    = simplElim size (snocSub sub $ simplElim size sub $ Ann s a) (Ann t b)

    | otherwise
    = App (simplElim size sub f) (simplTerm size sub s)

simplElim size sub (Sel s z)
    | Ann (Mul x _) (Sgm _ a _) <- s
    , "fst" <- z
    = simplElim size sub (Ann x a)

    | Ann (Mul x y) (Sgm _ a b) <- s
    , "snd" <- z
    = simplElim size (snocSub sub $ simplElim size sub $ Ann x a) (Ann (weaken wk1 y) b)

    | otherwise
    = Sel (simplElim size sub s) z

simplElim size sub (Swh e m ts)
    | Ann (Lbl l) (Fin ls) <- e
    , Just t <- Map.lookup l ts
    = Ann (simplTerm size sub t) (simplTerm size sub $ Emb $ Ann m (Fin ls ~~> Uni) @@ Lbl l)

    | otherwise
    = Swh (simplElim size sub e) (simplTerm size sub m) (fmap (simplTerm size sub) ts)

simplElim size sub (DeI e m x y z)
    -- can and should we optimize here?
    -- at least when e is Ann De1 Dsc?
    | otherwise
    = DeI (simplElim size sub e) (simplTerm size sub m) (simplTerm size sub x) (simplTerm size sub y) (simplTerm size sub z)

simplElim size sub (Ind e m t)
    -- can and should we optimize here?
    | otherwise
    = Ind (simplElim size sub e) (simplTerm size sub m) (simplTerm size sub t)

simplElim size sub (Ann t s)
    | otherwise
    = Ann (simplTerm size sub t) (simplTerm size sub s)

shouldInline :: Elim ctx -> Bool
shouldInline (Var _)         = True
shouldInline (Gbl _)         = True
shouldInline (Ann De1 _)     = True
shouldInline (Ann (Lbl _) _) = True
shouldInline (Ann Uni _)     = True
shouldInline (Ann Dsc _)     = True
shouldInline _               = False
