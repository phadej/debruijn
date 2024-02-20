module Main (main) where

import Test.Tasty       (TestName, TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, testCaseSteps, (@?=))

import NanoTT
import NanoTT.Base

main :: IO ()
main = defaultMain $ testGroup "nanott"
    [ testGroup "checking"
        [ testInfer "id"  exprId
        , testInfer "id-spl-quo" exprIdSplQuo
        , testInfer "quo-id" exprQuoId
        , testInfer "refl-id-1" exprReflId1
        , testInfer "refl-id-2" exprReflId2
        , testInfer "refl-id-3" exprReflId3
        , testInfer "refl-id-4" exprReflId4
        , testInfer "example-01" exprReflEx
        , testIllTyped "example-02" exprReflExIll
        ]
    , testGroup "staging"
        [ testStage "id" exprId
        -- , testStage "spl-quo" exprIdSplQuo -- not the same, there is top-level quote
        , testStage "quo-id" exprQuoId
        , testStage "refl-id-1" exprReflId1
        ]
    , testGroup "conversion"
        [ testCaseSteps "pi" $ \_ -> do
            assertConvTerm    vcodUni (Quo $ Pie Uni Uni) (Quo $ Pie Uni Uni)
            assertNotConvTerm vcodUni (Quo $ Pie Uni Uni) (Quo $ Pie Uni One)

        , testCaseSteps "app" $ \_ -> do
            assertConvElim exprId exprId
            assertConvTerm vcodUni
                (Quo $ Emb $ exprId @@ Uni @@ One)
                (Quo $ Emb $ exprId @@ Uni @@ One)
        ]
    ]

testInfer :: TestName -> Elim EmptyCtx -> TestTree
testInfer name e = testCaseSteps name $ \info -> do
    case runLintM (infer emptyLintEnv e) of
        Left err -> assertFailure err
        Right nty -> case quoteTerm SZ nty of
            Left err -> assertFailure err
            Right ty -> info $ show ty

testIllTyped :: TestName -> Elim EmptyCtx -> TestTree
testIllTyped name e = testCaseSteps name $ \info -> do
    case runLintM (infer emptyLintEnv e) of
        Left err  -> info err
        Right nty -> assertFailure (show nty)

testStage :: TestName -> Elim EmptyCtx -> TestTree
testStage name e = testCaseSteps name $ \_info -> do
    case quoteSElim NZ SZ (stageElim SZ EmptyEnv e) of
        Left err -> assertFailure err
        Right e' -> do
            -- traceShowM (stageElim SZ EmptyEnv e)
            show e' @?= show e

assertConvTerm :: VTerm EmptyCtx -> Term EmptyCtx -> Term EmptyCtx -> IO ()
assertConvTerm ty t s = do
    let t' = evalTerm SZ EmptyEnv t
    let s' = evalTerm SZ EmptyEnv s
    case convTerm emptyConvEnv ty t' s' of
        Right () -> return ()
        Left err -> assertFailure err

assertNotConvTerm :: VTerm EmptyCtx -> Term EmptyCtx -> Term EmptyCtx -> IO ()
assertNotConvTerm ty t s = do
    let t' = evalTerm SZ EmptyEnv t
    let s' = evalTerm SZ EmptyEnv s
    case convTerm emptyConvEnv ty t' s' of
        Right () -> assertFailure "convertible"
        Left _   -> return ()

assertConvElim :: Elim EmptyCtx -> Elim EmptyCtx -> IO ()
assertConvElim t s = do
    let t' = evalElim SZ EmptyEnv t
    let s' = evalElim SZ EmptyEnv s
    case convElim emptyConvEnv t' s' of
        Right _ -> return ()
        Left err -> assertFailure err

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

-- (\ _ x ->  x) : (A : U) -> A -> A)
exprId :: Elim ctx
exprId = Ann
    (Lam $ Lam var0)
    typeId

-- (\ _ x ->  $ [| x |]) : (A : U) -> A -> A)
exprIdSplQuo :: Elim ctx
exprIdSplQuo = Ann
    (Lam $ Lam $ Emb $ Spl $ Ann (Quo var0) (Cod (Quo var1)))
    typeId

-- (\_ x -> x) : (A : Code [| U |]) -> Code A -> Code A
exprQuoId :: Elim ctx
exprQuoId = Ann
    (Lam $ Lam $ var0)
    (Pie (Cod (Quo Uni)) $ Pie (Cod var0) (Cod var1))

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

exprReflEx :: Elim ctx
exprReflEx =
    Let (Ann Ast One) $
    Spl (Let (Ann Rfl (Equ (Cod (Quo One)) (Quo var0) (Quo var0))) $
        Ann (Quo Ast) (Cod (Quo One)))

exprReflExIll :: Elim ctx
exprReflExIll =
    Let (Ann Ast One) $
    Let (Ann Ast One) $
    Spl (Let (Ann Rfl (Equ (Cod (Quo One)) (Quo var0) (Quo var1))) $
        Ann (Quo Ast) (Cod (Quo One)))
