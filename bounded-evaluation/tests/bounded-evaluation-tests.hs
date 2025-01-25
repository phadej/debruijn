module Main (main) where

import Test.Tasty       (TestName, TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, testCaseSteps, (@?=))

import BoundedEvaluation
import BoundedEvaluation.Term
import BoundedEvaluation.Base

main :: IO ()
main = do
    q <- newStats
    vInd <- eval q emptyEvalEnv ind
    res <- conv q SZ vInd vInd
    print res
