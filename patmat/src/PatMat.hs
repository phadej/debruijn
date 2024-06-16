{-# LANGUAGE PolyKinds #-}
module PatMat (module PatMat) where

import Data.Kind (Type)

import DeBruijn

type List a = [a]

singleton :: a -> List a
singleton x = [x]

type ConName = String

type Expr :: ctx -> Type
data Expr ctx where
    Var :: Idx ctx -> Expr ctx
    Lam :: Expr (S ctx) -> Expr ctx
    Mch :: Expr ctx -> [Alt ctx] -> Expr ctx 

instance Weaken Expr where
    weaken wk (Var x)      = Var (weaken wk x)
    weaken wk (Lam t)      = Lam (weaken (KeepWk wk) t)
    weaken wk (Mch e alts) = Mch (weaken wk e) (map (weaken wk) alts) 

data Bind ctx ctx' where
    Bind :: Bind ctx (S ctx)

class Binder bind where
    nudge :: Wk n m -> bind n p -> Nudged bind p m

data Nudged bind p m where
    Nudged :: Wk p q -> bind m q -> Nudged bind p m

instance Binder Bind where
    nudge wk Bind = Nudged (KeepWk wk) Bind

instance Binder bind => Binder (Path bind) where
    nudge wk End = Nudged wk End
    nudge wk (Cons b bs) = case nudge wk b of
        Nudged wk' b' -> case nudge wk' bs of
            Nudged wk'' bs' -> Nudged wk'' (Cons b' bs')

instance Binder Pat where
    nudge wk VarP         = Nudged (KeepWk wk) VarP
    nudge wk (ConP cn ps) = case nudge wk ps of
        Nudged wk' ps' -> Nudged wk' (ConP cn ps')

type Alt :: Ctx -> Type
data Alt ctx where
    ConA :: ConName -> Path Bind ctx ctx' -> Expr ctx' -> Alt ctx
    VarA :: Expr (S ctx) -> Alt ctx

instance Weaken Alt where
    weaken wk (VarA e)       = VarA (weaken (KeepWk wk) e)
    weaken wk (ConA cn bs e) = ConA cn undefined $ error "TODO" cn bs 

type Pat :: Ctx -> Ctx -> Type
data Pat n m where
    VarP :: Pat ctx (S ctx)
    ConP :: ConName -> Path Pat ctx ctx' -> Pat ctx ctx' 

type Clause :: Ctx -> Type
data Clause ctx where
    Clause :: Pat ctx ctx' -> Expr ctx' -> Clause ctx

-- | Transitive-reflexive closure.
type Path :: (k -> k -> Type) -> k -> k -> Type
data Path p a b where
    End  :: Path p a a
    Cons :: p a b -> Path p b c -> Path p a c

append :: Path p xs ys -> Path p ys zs -> Path p xs zs
append End         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

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
                    [ weaken wk $ ClauseN (append ps qs) e
                    | Group ps qs e <- sub
                    ]

    vg' :: [Alt ctx]
    vg' = case vg of
        Nothing -> []
        Just (VarGroup ps e) -> singleton $
            VarA $
            match (map (weaken wk1) xs) $ singleton $ ClauseN ps e

data Aux ctx where
    Aux :: Path Bind ctx ctx' -> [Idx ctx'] -> Wk ctx ctx' -> Aux ctx

helper :: Path Pat ctx ctx' -> Aux ctx
helper = undefined

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
