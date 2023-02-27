{-# LANGUAGE Trustworthy #-}
module DeBruijn.Size (
    Size (SZ, SS),
    unSS,
    sizeToInt,
    -- * Common sizes
    pattern S1,
    pattern S2,
    pattern S3,
    pattern S4,
    pattern S5,
    pattern S6,
    pattern S7,
    pattern S8,
    pattern S9,
) where

import DeBruijn.Internal.Size
