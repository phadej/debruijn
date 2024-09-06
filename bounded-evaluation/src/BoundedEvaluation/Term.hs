module BoundedEvaluation.Term (
    Term (..),
    (@@),
    apps,
    -- * Examples
    two,
    ind,
    ex1,
    ex2,
    ex3,
    ex4,
) where

import BoundedEvaluation.Base
import BoundedEvaluation.Pretty

-- $setup
--
-- >>> import BoundedEvaluation.Base
-- >>> import BoundedEvaluation.Pretty

-------------------------------------------------------------------------------
-- Syntax
-------------------------------------------------------------------------------

type Term :: Ctx -> Type
data Term ctx where
   Var :: Idx ctx -> Term ctx                            -- ^ variable: @x@
   Lam :: Term (S ctx) -> Term ctx                       -- ^ lambda: @λ x → t@
   App :: Term ctx -> Term ctx -> Term ctx               -- ^ application: @f t@
   Let :: Term ctx -> Term (S ctx) -> Term ctx           -- ^ let expression: @let x = e in e'@
   Zer :: Term ctx
   Suc :: Term ctx -> Term ctx
   Mch :: Term ctx -> Term ctx -> Term (S ctx) -> Term ctx
   Fix :: Term (S ctx) -> Term ctx

deriving instance Show (Term ctx)

(@@) :: Term ctx -> Term ctx -> Term ctx
(@@) = App

apps :: Term ctx -> [Term ctx] -> Term ctx
apps = foldl' App

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty Term where
    pretty env (Var x)     = lookupEnv x env
    pretty env (Lam t)     = withFresh "x" $ \x ->
        prettyLam (env :> x) (x :) t
    pretty env (App f t)   =
        prettyApp env f [pretty env t]
    pretty env (Let t s)   = withFresh "x" $ \x ->
        prettyLet (env :> x) (ppList1 x [pretty env t] :) s
    pretty _   Zer         = "zero"
    pretty env (Suc t)     = ppList1 "succ" [pretty env t]
    pretty env (Mch t n s) = withFresh "n" $ \m -> ppList1 "case"
        [ pretty env t
        , ppList1 "zero"               [pretty env n]
        , ppList1 (ppList1 "succ" [m]) [pretty (env :> m) s]
        ]
    pretty env (Fix t) = withFresh "rec" $ \r ->
        ppList1 "fix" [r, pretty (env :> r) t]

prettyApp :: Env ctx Doc -> Term ctx -> [Doc] -> Doc
prettyApp env (App f t) ts = prettyApp env f (pretty env t : ts)
prettyApp env f         ts = ppList1 (pretty env f) ts

prettyLam :: Env ctx Doc -> ([Doc] -> [Doc]) -> Term ctx -> Doc
prettyLam env xs (Lam t) = withFresh "x" $ \x -> prettyLam (env :> x) (xs . (x :)) t
prettyLam env xs t       = ppList1 "fn" [ppList (xs []), pretty env t]

prettyLet :: Env ctx Doc -> ([Doc] -> [Doc]) -> Term ctx -> Doc
prettyLet env xs (Let t s) = withFresh "x" $ \x -> prettyLet (env :> x) (xs . (ppList1 x [pretty env t] :)) s
prettyLet env xs t         = ppList1 "let" (xs [pretty env t])

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

-- | Two
--
-- >>> pretty EmptyEnv two
-- (succ (succ zero))
two :: Term ctx
two = Suc (Suc Zer)

-- | Natural number induction
--
-- >>> pretty EmptyEnv ind
-- (fn
--    (x_0 x_1)
--    (fix
--       rec_2
--       (fn (x_3) (case x_3 (zero x_0) ((succ n_4) (x_1 (rec_2 n_4)))))))
--
ind :: Term ctx
ind = Lam $ Lam $ Fix $ Lam $ Mch (Var IZ)
    (Var I3)
    (App (Var I3) (App (Var I2) (Var IZ)))

add :: Term (S (S ctx)) -> Term ctx
add i = Lam $ Lam $ i `App` Var IZ `App` (Lam $ Suc $ Var IZ) `App` Var I1

mult :: Term (S (S ctx)) -> Term (S (S ctx)) -> Term ctx
mult i a = Lam $ Lam $ i `App` Zer `App` (App a (Var IZ)) `App` Var I1

-- | Addition example
--
-- @2 + 2 + 2@
--
-- >>> pretty EmptyEnv ex1
-- (let
--    (x_0 (succ (succ zero)))
--    (x_1
--       (fn
--          (x_3 x_4)
--          (fix
--             rec_5
--             (fn (x_6) (case x_6 (zero x_3) ((succ n_7) (x_4 (rec_5 n_7))))))))
--    (x_2 (fn (x_8 x_9) (x_1 x_9 (fn (x_10) (succ x_10)) x_8)))
--    (x_2 x_0 (x_2 x_0 x_0)))
--
ex1 :: Term ctx
ex1 =
    Let two $
    Let ind $
    Let (add (Var I2)) $
    Var IZ @@ Var I2 @@ (Var IZ @@ Var I2 @@ Var I2)

-- | Multiplication example
--
-- @2 * 3@
--
-- >>> pretty EmptyEnv ex2
-- (let
--    (x_0 (succ (succ zero)))
--    (x_1 (succ x_0))
--    (x_2
--       (fn
--          (x_5 x_6)
--          (fix
--             rec_7
--             (fn (x_8) (case x_8 (zero x_5) ((succ n_9) (x_6 (rec_7 n_9))))))))
--    (x_3 (fn (x_10 x_11) (x_2 x_11 (fn (x_12) (succ x_12)) x_10)))
--    (x_4 (fn (x_13 x_14) (x_2 zero (x_3 x_14) x_13)))
--    (x_4 x_0 x_1))
--
ex2 :: Term ctx
ex2 =
    Let two $
    Let (Suc (Var IZ)) $
    Let ind $
    Let (add (Var I2)) $
    Let (mult (Var I3) (Var I2)) $
    Var IZ @@ Var I4 @@ Var I3

-- | Infinite natural number
--
-- @ω = fix (\x -> succ x)@
--
-- >>> pretty EmptyEnv ex3
-- (fix rec_0 (succ rec_0))
--
ex3 :: Term ctx
ex3 = Fix $ Suc (Var IZ)

-- | Loop
--
-- @loop = fix (\x -> x)@
--
-- >>> pretty EmptyEnv ex4
-- (fix rec_0 rec_0)
ex4 :: Term ctx
ex4 = Fix (Var IZ)
