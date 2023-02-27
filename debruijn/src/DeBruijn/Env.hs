{-# LANGUAGE Trustworthy #-}
module DeBruijn.Env (
    Env (EmptyEnv, (:>)),
    lookupEnv,
    sizeEnv,
    tabulateEnv,
) where

import DeBruijn.Internal.Env
