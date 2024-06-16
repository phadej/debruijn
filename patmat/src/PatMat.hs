module PatMat (module PatMat) where

import Data.Kind (Type)

import DeBruijn
import Path
import Binder
import Name

type List a = [a]

singleton :: a -> List a
singleton x = [x]

type ConName = String

type Constructor :: Ctx -> Type
data Constructor arity where
    Constructor :: String -> !(Size arity) -> Constructor arity

type Expr :: Ctx -> Type
data Expr ctx where
    Var :: Idx ctx -> Expr ctx
    Lam :: Expr (S ctx) -> Expr ctx
    Mch :: Expr ctx -> [Alt ctx] -> Expr ctx 

instance Weaken Expr where
    weaken wk (Var x)    = Var (weaken wk x)
    weaken wk (Lam t)    = Lam (weaken (KeepWk wk) t)
    weaken wk (Mch e ts) = Mch (weaken wk e) (map (weaken wk) ts) 



type Alt :: Ctx -> Type
data Alt ctx where
    ConA :: ConName -> Path Bind ctx ctx' -> Expr ctx' -> Alt ctx
    VarA :: Expr (S ctx) -> Alt ctx

instance Weaken Alt where
    weaken wk (VarA e)       = VarA (weaken (KeepWk wk) e)
    weaken wk (ConA cn bs e) = case nudge wk bs of
        Nudged wk' bs' -> ConA cn bs' (weaken wk' e)

type Pat :: Ctx -> Ctx -> Type
data Pat n m where
    VarP :: Pat ctx (S ctx)
    ConP :: ConName -> Path Pat ctx ctx' -> Pat ctx ctx' 

instance Binder Pat where
    nudge wk VarP         = Nudged (KeepWk wk) VarP
    nudge wk (ConP cn ps) = case nudge wk ps of
        Nudged wk' ps' -> Nudged wk' (ConP cn ps')

type Clause :: Ctx -> Type
data Clause ctx where
    Clause :: Pat ctx ctx' -> Expr ctx' -> Clause ctx

type ClauseN :: Ctx -> Type
data ClauseN ctx where
    ClauseN :: Path Pat ctx ctx' -> Expr ctx' -> ClauseN ctx

instance Weaken ClauseN where
    weaken wk (ClauseN ps e) = case nudge wk ps of
        Nudged wk' ps' -> ClauseN ps' (weaken wk' e)

type ClauseN1 :: Ctx -> Type
data ClauseN1 ctx where
    ClauseN1 :: Pat ctx ctx' -> Path Pat ctx' ctx'' -> Expr ctx'' -> ClauseN1 ctx

match :: [Idx ctx] -> [ClauseN ctx] -> Expr ctx
match _      [] = error "no clauses"
match []     (ClauseN End e : _) = e
match []     (ClauseN (Cons p ps) e : cs) = error "Intro" p ps e cs
match (x:xs) (ClauseN (Cons p ps) e : cs) = Mch (Var x) $ alts xs (ClauseN1 p ps e : map expand cs)
match (_:_)  (ClauseN End _ : _) = error "panic"

expand :: ClauseN ctx -> ClauseN1 ctx
expand (ClauseN (Cons p ps) e) = ClauseN1 p ps e
expand (ClauseN End e)         = error "TODO: expand" e

alts :: forall ctx. [Idx ctx] -> [ClauseN1 ctx] -> [Alt ctx]
alts _  []                       = []
alts xs (ClauseN1 VarP ps e : _) =
    singleton $
    VarA $
    match (map (weaken wk1) xs) $ singleton $ ClauseN ps e
alts xs (c@(ClauseN1 (ConP _ _) _ _) : cs) =
    gs' ++ vg'
  where
    (gs, vg) = group (c:cs)

    gs' :: [Alt ctx]
    gs' = do
        (cn, sub@(Group ps _ _ : _)) <- gs
        case helper ps of
            Aux binds ys wk -> do
                return $ ConA cn binds $ match
                    (ys ++ map (weaken wk) xs)
                    [ weaken wk $ ClauseN (append ps' qs) e
                    | Group ps' qs e <- sub
                    ]

    vg' :: [Alt ctx]
    vg' = case vg of
        Nothing -> []
        Just (VarGroup ps e) -> singleton $
            VarA $
            match (map (weaken wk1) xs) $ singleton $ ClauseN ps e

data Aux ctx where
    Aux :: Path Bind ctx ctx' -> [Idx ctx'] -> Wk ctx ctx' -> Aux ctx

helper :: Path Pat ctxA ctxB -> Aux ctx
helper End                = Aux End [] IdWk
helper (Cons p ps) = case helper ps of
    Aux ps' xs wk -> Aux (Cons (Bind (mkName p)) (helper2 ps')) (IZ : map (weaken wk1) xs) (SkipWk wk)

mkName :: Pat ctx ctx' -> Name
mkName _ = Name "ds"

helper2 :: Path Bind ctx ctx' -> Path Bind (S ctx) (S ctx')
helper2 End                = End
helper2 (Cons (Bind n) ps) = Cons (Bind n) (helper2 ps)

data Group ctx where
    Group :: Path Pat ctx ctx' -> Path Pat ctx' ctx'' -> Expr ctx'' -> Group ctx

type VarGroup :: Ctx -> Type
data VarGroup ctx where
    VarGroup :: Path Pat (S ctx) ctx' -> Expr ctx' -> VarGroup ctx

group :: [ClauseN1 ctx] -> ([(ConName, [Group ctx])], Maybe (VarGroup ctx))
group [] = ([], Nothing)
group (ClauseN1 VarP         ps e : _)  = ([], Just (VarGroup ps e))
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
