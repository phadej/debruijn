{-# LANGUAGE Trustworthy #-}
-- | de Bruijn indices for well-scoped terms.
module DeBruijn.Idx (
    -- * de Bruijn indices
    Idx (IZ, IS),
    absurdIdx,
    unIdx,
    idxToInt,
    -- * Common indices
    pattern I1,
    pattern I2,
    pattern I3,
    pattern I4,
    pattern I5,
    pattern I6,
    pattern I7,
    pattern I8,
    pattern I9,
) where


import DeBruijn.Internal.Idx
