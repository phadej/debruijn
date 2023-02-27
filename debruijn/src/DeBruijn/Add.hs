{-# LANGUAGE Trustworthy #-}
module DeBruijn.Add (
    Add (AZ, AS),
    addToInt,
    addToSize,
    adding,
    -- * Lemmas
    rzeroAdd,
    unrzeroAdd,
    lzeroAdd,
    unlzeroAdd,
    keepAdd,
    unkeepAdd,
    swapAdd,
    unswapAdd,
) where

import DeBruijn.Internal.Add
