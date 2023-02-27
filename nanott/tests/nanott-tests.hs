module Main (main) where

import Test.Tasty       (TestName, TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, testCaseSteps)

import NanoTT
import NanoTT.Base

main :: IO ()
main = defaultMain $ testGroup "nanott"
    [ testInfer "id"  exprId
    , testInfer "id-spl-quo" exprIdSplQuo
    , testInfer "quo-id" exprQuoId
    , testInfer "refl-id-1" exprReflId1
    , testInfer "refl-id-2" exprReflId2
    , testInfer "refl-id-3" exprReflId3
    , testInfer "refl-id-4" exprReflId4
    ]


testInfer :: TestName -> Elim EmptyCtx -> TestTree
testInfer name e = testCaseSteps name $ \info -> do
    case infer emptyLintEnv e of
        Left err -> assertFailure err
        Right nty -> case quoteTerm SZ nty of
            Left err -> assertFailure err
            Right ty -> info $ show ty

-------------------------------------------------------------------------------
-- Convenience operators
-------------------------------------------------------------------------------

class    FromElim t    where fromElim :: Elim ctx -> t ctx
instance FromElim Term where fromElim = Emb
instance FromElim Elim where fromElim = id

var' :: FromElim t => Idx ctx -> t ctx
var' = fromElim . Var

var0 :: FromElim t => t (S ctx)
var0 = var' IZ

var1 :: FromElim t => t (S (S ctx))
var1 = var' (IS IZ)

-- var2 :: FromElim t => t (S (S (S ctx)))
-- var2 = var' (IS (IS IZ))

infixl 1 @@
(@@) :: FromElim t => Elim ctx -> Term ctx -> t ctx
f @@ t = fromElim (App f t)

-------------------------------------------------------------------------------
-- Expressions
-------------------------------------------------------------------------------

typeId :: Term ctx
typeId = Pie Uni $ Pie var0 var1

exprId :: Elim ctx
exprId = Ann
    (Lam $ Lam var0)
    typeId

exprIdSplQuo :: Elim ctx
exprIdSplQuo = Ann
    (Lam $ Lam $ Emb $ Spl $ Ann (Quo var0) (Cod (Quo var1)))
    typeId

exprQuoId :: Elim ctx
exprQuoId = Ann
    (Lam $ Lam $ var0)
    typeId

exprReflId1 :: Elim ctx
exprReflId1 = Ann Rfl $
    Equ typeId (Lam $ Lam $ var0) (Lam $ Lam $ var0)

exprReflId2 :: Elim ctx
exprReflId2 = Ann
    (Lam $ Emb $ Let (Ann Rfl $ Equ typeId var0 var0) (Ann Ast One))
    (Pie typeId One)

exprReflId3 :: Elim ctx
exprReflId3 = Ann
    (Lam $ Emb $ Let (Ann Rfl $ Equ typeId (Lam $ var1 @@ var0) var0) (Ann Ast One))
    (Pie typeId One)

exprReflId4 :: Elim ctx
exprReflId4 = Ann
    (Lam $ Emb $ Let (Ann Rfl $ Equ typeId var0 (Lam $ var1 @@ var0)) (Ann Ast One))
    (Pie typeId One)
