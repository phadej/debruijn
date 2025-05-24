module Main (main) where

import Test.Tasty (defaultMain, testGroup)
import Numeric.Natural (Natural)
import Test.Tasty.QuickCheck

import DeBruijn

main :: IO ()
main = defaultMain $ testGroup "debruijn"
    [ testProperty "wk-comp" $
        forAllShrink genWkNatural shrinkIntegral $ \n ->
        forAllShrink genWkNatural shrinkIntegral $ \m ->
        propWkComposition n m
    , testProperty "wk-idx" $ 
        forAllShrink genIdxNatural shrinkIntegral $ \x ->
        forAllShrink genWkNatural shrinkIntegral $ \w ->
        propWkIdx x w
    ]

genWkNatural :: Gen Natural
genWkNatural = oneof
    [ arbitrarySizedNatural
    ]

genIdxNatural :: Gen Natural
genIdxNatural = oneof
    [ arbitrarySizedNatural
    ]

-------------------------------------------------------------------------------
-- Some weakening
-------------------------------------------------------------------------------

data SomeWk where
    SomeWk :: Wk n m -> SomeWk

deriving instance Show SomeWk

instance Eq SomeWk where
    SomeWk w == SomeWk w' = eqWk w w'

eqWk :: Wk n m -> Wk n' m' -> Bool
eqWk IdWk       IdWk        = True
eqWk (SkipWk w) (SkipWk w') = eqWk w w'
eqWk (KeepWk w) (KeepWk w') = eqWk w w'
eqWk _ _ = False

keepSomeWk :: SomeWk -> SomeWk
keepSomeWk (SomeWk w) = SomeWk (KeepWk w)

skipSomeWk :: SomeWk -> SomeWk
skipSomeWk (SomeWk w) = SomeWk (SkipWk w)

compSomeWk :: SomeWk -> SomeWk -> SomeWk
compSomeWk w                   (SomeWk IdWk)        = w
compSomeWk w                   (SomeWk (SkipWk w')) = skipSomeWk (compSomeWk w (SomeWk w'))
compSomeWk (SomeWk IdWk)    w'@(SomeWk (KeepWk _))  = w'
compSomeWk (SomeWk (SkipWk w)) (SomeWk (KeepWk w')) = skipSomeWk (compSomeWk (SomeWk w) (SomeWk w'))
compSomeWk (SomeWk (KeepWk w)) (SomeWk (KeepWk w')) = keepSomeWk (compSomeWk (SomeWk w) (SomeWk w'))

naturalToSomeWk :: Natural -> SomeWk
naturalToSomeWk n
    | n <= 0    = SomeWk IdWk
    | odd n     = skipSomeWk (naturalToSomeWk (n `div` 2))
    | otherwise = keepSomeWk (naturalToSomeWk (n `div` 2))

-------------------------------------------------------------------------------
-- Some index
-------------------------------------------------------------------------------

data SomeIdx where
    SomeIdx :: Idx n -> SomeIdx

deriving instance Show SomeIdx

instance Eq SomeIdx where
    SomeIdx i == SomeIdx j = eqIdx i j

eqIdx :: Idx n -> Idx m -> Bool
eqIdx IZ     IZ     = True
eqIdx (IS i) (IS j) = eqIdx i j
eqIdx _ _ = False

someIS :: SomeIdx -> SomeIdx
someIS (SomeIdx i) = SomeIdx (IS i)

weakenSomeIdx :: SomeWk -> SomeIdx -> SomeIdx
weakenSomeIdx (SomeWk IdWk)       i                = i
weakenSomeIdx (SomeWk (SkipWk w)) i                = someIS (weakenSomeIdx (SomeWk w) i)
weakenSomeIdx (SomeWk (KeepWk _)) (SomeIdx IZ)     = SomeIdx IZ
weakenSomeIdx (SomeWk (KeepWk w)) (SomeIdx (IS i)) = someIS (weakenSomeIdx (SomeWk w) (SomeIdx i))

naturalToSomeIdx :: Natural -> SomeIdx
naturalToSomeIdx n
    | n <= 0    = SomeIdx IZ
    | otherwise = someIS (naturalToSomeIdx (n - 1))

-------------------------------------------------------------------------------
-- Composition of two weakenings
-------------------------------------------------------------------------------

-- compatible pair of weakenings
data PairWk where
    PairWk :: Wk n m -> Wk m p -> PairWk

pairSomeWk :: SomeWk -> SomeWk -> PairWk
pairSomeWk (SomeWk w) (SomeWk w') = pairSomeWk' w w'

pairSomeWk' :: Wk n m -> Wk p q -> PairWk
pairSomeWk' w          IdWk        = PairWk w IdWk
pairSomeWk' w          (SkipWk w') = case pairSomeWk' w w' of PairWk u u' -> PairWk u (SkipWk u') 
pairSomeWk' IdWk       (KeepWk w') = PairWk IdWk (KeepWk w')
pairSomeWk' (SkipWk w) (KeepWk w') = case pairSomeWk' w w' of PairWk u u' -> PairWk (SkipWk u) (KeepWk u')
pairSomeWk' (KeepWk w) (KeepWk w') = case pairSomeWk' w w' of PairWk u u' -> PairWk (KeepWk u) (KeepWk u')

propWkComposition :: Natural -> Natural -> Property
propWkComposition n n' = compSomeWk w w' === case pairSomeWk w w' of
    PairWk u u' -> SomeWk (compWk u u')
  where
    w  = naturalToSomeWk n
    w' = naturalToSomeWk n'

-------------------------------------------------------------------------------
-- Weakening of an index
-------------------------------------------------------------------------------

-- compatible weakening and index
data SomeIdxWk where
    SomeIdxWk :: Wk ctx ctx' -> Idx ctx -> SomeIdxWk

someIdxWk :: SomeWk -> SomeIdx -> SomeIdxWk
someIdxWk (SomeWk w) (SomeIdx x) = someIdxWk' w x

someIdxWk' :: Wk n m -> Idx p -> SomeIdxWk
someIdxWk' IdWk i            = SomeIdxWk IdWk i
someIdxWk' (SkipWk w) i      = case someIdxWk' w i of SomeIdxWk w' i' -> SomeIdxWk (SkipWk w') i'
someIdxWk' (KeepWk w) IZ     = SomeIdxWk (KeepWk w) IZ
someIdxWk' (KeepWk w) (IS i) = case someIdxWk' w i of SomeIdxWk w' i' -> SomeIdxWk (KeepWk w') (IS i')

propWkIdx :: Natural -> Natural -> Property
propWkIdx x w = weakenSomeIdx w' x' === case someIdxWk w' x' of
    SomeIdxWk w'' x'' -> SomeIdx (weakenIdx w'' x'')
  where
    x' = naturalToSomeIdx x
    w' = naturalToSomeWk w
