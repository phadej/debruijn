{-# OPTIONS_GHC -Wno-name-shadowing #-}
module PatMat (module PatMat) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.GADT.Compare (GEq (..))

-- import Debug.Trace

import DeBruijn

import Path
import Constructor
import Binder
import Name

type List a = [a]

singleton :: a -> List a
singleton x = [x]

type ConName = String

type Expr :: Ctx -> Type
data Expr ctx where
    Var :: Idx ctx -> Expr ctx
    Lam :: Expr (S ctx) -> Expr ctx
    App :: Expr ctx -> Expr ctx -> Expr ctx
    Mch :: Expr ctx -> [Alt ctx] -> Expr ctx

deriving instance Show (Expr ctx)
deriving instance Show (Alt ctx)

instance Weaken Expr where
    weaken wk (Var x)    = Var (weaken wk x)
    weaken wk (Lam t)    = Lam (weaken (keep wk) t)
    weaken wk (App f t)  = App (weaken wk f) (weaken wk t)
    weaken wk (Mch e ts) = Mch (weaken wk e) (map (weaken wk) ts)

instance Rename Expr where
    rename wk (Var x)    = Var (rename wk x)
    rename wk (Lam t)    = Lam (rename (keep wk) t)
    rename wk (App f t)  = App (rename wk f) (rename wk t)
    rename wk (Mch e ts) = Mch (rename wk e) (map (rename wk) ts)

type Alt :: Ctx -> Type
data Alt ctx where
    ConA :: Constructor arity -> PathN Bind arity ctx ctx' -> Expr ctx' -> Alt ctx
    VarA :: !Name -> Expr (S ctx) -> Alt ctx

instance Weaken Alt where
    weaken wk (VarA n e)     = VarA n (weaken (keep wk) e)
    weaken wk (ConA cn bs e) = case nudge wk bs of
        Nudged wk' bs' -> ConA cn bs' (weaken wk' e)

instance Rename Alt where
    rename wk (VarA n e)     = VarA n (rename (keep wk) e)
    rename wk (ConA cn bs e) = case nudge wk bs of
        Nudged wk' bs' -> ConA cn bs' (rename wk' e)

type Pat :: Ctx -> Ctx -> Type
data Pat n m where
    VarP :: !Name -> Pat ctx (S ctx)
    ConP :: Constructor arity -> PathN Pat arity ctx ctx' -> Pat ctx ctx'

deriving instance Show (Pat ctx ctx')

instance Binder Pat where
    nudge wk (VarP n)     = Nudged (keep wk) (VarP n)
    nudge wk (ConP cn ps) = case nudge wk ps of
        Nudged wk' ps' -> Nudged wk' (ConP cn ps')

type Clause :: Ctx -> Type
data Clause ctx where
    Clause :: Pat ctx ctx' -> Expr ctx' -> Clause ctx

type ClauseN :: Ctx -> Type
data ClauseN ctx where
    ClauseN :: Path Pat ctx ctx' -> Expr ctx' -> ClauseN ctx

type ClauseN1 :: Ctx -> Type
data ClauseN1 ctx where
    ClauseN1 :: Pat ctx ctx' -> Path Pat ctx' ctx'' -> Expr ctx'' -> ClauseN1 ctx

expand :: ClauseN ctx -> ClauseN1 ctx
expand (ClauseN (Cons p ps) e) = ClauseN1 p    ps e
expand (ClauseN End e)         = ClauseN1 (VarP "eta") End (weaken wk1 e)

instance Weaken ClauseN where
    weaken wk (ClauseN ps e) = case nudge wk ps of
        Nudged wk' ps' -> ClauseN ps' (weaken wk' e)

match :: Size ctx -> [Idx ctx] -> [ClauseN ctx] -> Expr ctx
match _ _        [] = error "no clauses"
match _ []       (ClauseN End e : _) = e
match _ (_:_)    (ClauseN End _ : _) = error "panic"
match s []    cs@(ClauseN (Cons _ _) _ : _) = Lam $ match (SS s) [IZ] $ map (weaken wk1) cs
match s (x:xs)   (ClauseN (Cons p ps) e : cs) = Mch (Var x) $ alts s xs (ClauseN1 p ps e : map expand cs)

data Group ctx where
    Group :: Constructor arity -> [Group' ctx arity] -> Group ctx

data Group' ctx arity where
    Group' :: PathN Pat arity ctx ctx' -> Path Pat ctx' ctx'' -> Expr ctx'' -> Group' ctx arity

alts :: Size ctx -> [Idx ctx] -> [ClauseN1 ctx] -> [Alt ctx]
alts = alts

{-
group :: [{- ClauseN1 ctx -} ()] -> ([(ConName, [Group ctx])])
group = undefined
-}

insert :: Constructor arity -> PathN Pat arity ctx ctx' -> Path Pat ctx' ctx'' -> Expr ctx'' -> [Group ctx] -> [Group ctx]
insert cn ps qs e [] =
    [Group cn [Group' ps qs e]]
insert cn ps qs e (g@(Group cn' gs) : rest) =
    case geq cn cn' of
        Nothing -> g : insert cn ps qs e rest

        Just Refl ->
            Group cn' (Group' ps qs e : gs) : rest

todo :: forall ctx. [Alt ctx]
todo = do
    Group cn@(Constructor _ arity) gs' <- gs
    case helper s arity of
        Aux s' binds ys wk -> do
            return $ ConA cn binds $ match s' (ys ++ map (weaken wk) xs)
                [ _
                | Group' ps qs e <- gs'
                ]
  where
    xs :: [Idx ctx]
    xs = undefined

    s :: Size ctx
    s = undefined

    gs :: [Group ctx]
    gs = undefined

mkBinds :: Constructor arity -> PathN Bind arity ctx ctx'
mkBinds (Constructor _ s) = go s where
    go :: Size arity -> PathN Bind arity ctx ctx'
    go SZ = undefined

data Aux ctx arity where
    Aux :: Size ctx' -> PathN Bind arity ctx ctx' -> [Idx ctx'] -> Wk ctx ctx' -> Aux ctx arity

helper :: Size ctx -> Size arity -> Aux ctx arity
helper s SZ = Aux s EndN [] IdWk

    
{-

alts :: forall ctx. Size ctx -> [Idx ctx] -> [ClauseN1 ctx] -> [Alt ctx]
alts _ _ []                            = []
alts s xs (ClauseN1 (VarP n) ps e : _) =
    singleton $
    VarA n $
    match (SS s) (map (weaken wk1) xs) $ singleton $ ClauseN ps e
alts s xs (c@(ClauseN1 (ConP _ _) _ _) : cs) =
    -- traceShow xs $ 
    gs' ++ vg'
  where
    (gs, vg) = group (c:cs)

    gs' :: [Alt ctx]
    gs' = do
        (cn, sub@(Group ps _ _ : _)) <- gs
        case helper s ps of
            Aux s' binds ys wk -> do
                return $ ConA cn binds $ match s'
                    (ys ++ map (weaken wk) xs)
                    [ weaken wk $ ClauseN (append ps' qs) e
                    | Group ps' qs e <- sub
                    ]

    vg' :: [Alt ctx]
    vg' = case vg of
        Nothing -> []
        Just (VarGroup n ps e) -> singleton $
            VarA n $
            match (SS s) (map (weaken wk1) xs) $ singleton $ ClauseN ps e

data Aux ctx where
    Aux :: Size ctx' -> Path Bind ctx ctx' -> [Idx ctx'] -> Wk ctx ctx' -> Aux ctx

helper :: Size ctx -> Path Pat ctxA ctxB -> Aux ctx
helper s End                = Aux s End [] IdWk
helper s (Cons p ps) = case helper s ps of
    Aux s ps' xs wk -> Aux (SS s) (Cons (Bind (namePattern p)) (helper2 ps')) (map (weaken wk1) xs ++ [IZ]) (SkipWk wk)



helper2 :: Path Bind ctx ctx' -> Path Bind (S ctx) (S ctx')
helper2 End                = End
helper2 (Cons (Bind n) ps) = Cons (Bind n) (helper2 ps)


namePattern :: Pat ctx ctx' -> Name
namePattern (VarP n) = n
namePattern _        = Name "ds"


type VarGroup :: Ctx -> Type
data VarGroup ctx where
    VarGroup :: Name -> Path Pat (S ctx) ctx' -> Expr ctx' -> VarGroup ctx

group :: [ClauseN1 ctx] -> ([(ConName, [Group ctx])], Maybe (VarGroup ctx))
group [] = ([], Nothing)
group (ClauseN1 (VarP n)     ps e : _)  = ([], Just (VarGroup n ps e))
group (ClauseN1 (ConP cn ss) ps e : cs) =
    let (gs, vg) = group cs
    in (insert cn ss ps e gs, vg)

insert :: ConName -> Path Pat ctx ctx' -> Path Pat ctx' ctx'' -> Expr ctx'' -> [(ConName, [Group ctx])] -> [(ConName, [Group ctx])]
insert cn ps qs e [] = [(cn, [Group ps qs e])]
insert cn ps qs e ((cn', gs) : rest)
    | cn == cn'
    = (cn', Group ps qs e : gs) : rest

    | otherwise
    = (cn', gs) : insert cn ps qs e rest
-}

-------------------------------------------------------------------------------
-- examples
-------------------------------------------------------------------------------

demo1 :: Expr EmptyCtx
demo1 = match SZ [] $ singleton $ case clause1 of
    Clause p e -> ClauseN (Cons p End) e

clause1 :: Clause EmptyCtx
clause1 =
    Clause p $ Var IZ `App` Var (IS IZ) `App` Var (IS (IS IZ)) `App` Var (IS (IS (IS IZ)))
  where
    p = pairP (pairP (VarP "f") (VarP "x")) (pairP (VarP "y") (VarP "z"))

pairP :: Pat ctx ctx' -> Pat ctx' ctx'' -> Pat ctx ctx''
pairP p1 p2 = ConP (Constructor "tuple" S2) (ConsN p1 (ConsN p2 EndN))

pretty :: Expr EmptyCtx -> String
pretty e = prettyN EmptyEnv e ""

prettyN :: Env ctx String -> Expr ctx -> ShowS
prettyN env (Var x) = showString (lookupEnv x env)
prettyN env (Lam t) = showParen True $ showString "fn eta " . prettyN (env :> "eta") t
prettyN env (App f t) = showParen True $ prettyN env f . showChar ' ' . prettyN env t
prettyN env (Mch e alts) =
    showParen True $ showString "match" . showChar ' ' .
    prettyN env e . prettyA env alts

prettyA :: Env ctx String -> [Alt ctx] -> ShowS
prettyA _env [] = id
prettyA  env (t : ts) = showChar ' ' . showParen True (prettyAA env t) . prettyA env ts

prettyAA :: Env ctx' String -> Alt ctx' -> ShowS
prettyAA env (VarA (Name n) e) = showString n' . showChar ' ' . prettyN (env :> n') e
  where n' = fresh n env
prettyAA env (ConA cn bs e) = showCN cn . go env bs e
  where
    go :: Env ctx String -> PathN Bind arity ctx ctx' -> Expr ctx' -> ShowS
    go env' EndN                       e = showChar ' ' . prettyN env' e
    go env' (ConsN (Bind (Name n)) ps) e = showChar ' ' . showString n' . go (env' :> n') ps e
      where n' = fresh n env'

showCN :: Constructor arity -> ShowS
showCN (Constructor n s) = showString n . showChar '/' . shows (sizeToInt s)

fresh :: String -> Env ctx String -> String
fresh n env
    | elem n env = go 0
    | otherwise  = n
  where
    go :: Int -> String
    go i = let n' = n ++ show i in if elem n' env then go (i + 1) else n'
