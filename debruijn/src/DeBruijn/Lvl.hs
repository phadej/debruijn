{-# LANGUAGE Trustworthy #-}
module DeBruijn.Lvl (
    Lvl,
    lvlToIdx,
    lvlZ,
    idxToLvl,
    -- * Sinking
    Sinkable (..),
    sink,
    sinkSize,
    sinkAdd,
    mapSink,
    mapSinkSize,
    mapSinkAdd,
) where

import DeBruijn.Internal.Lvl
