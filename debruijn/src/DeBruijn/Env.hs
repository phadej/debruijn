{-# LANGUAGE Trustworthy #-}
module DeBruijn.Env (
    Env (EmptyEnv, (:>)),
    lookupEnv,
    sizeEnv,
    tabulateEnv,
    zipWithEnv,
) where

import DeBruijn.Internal.Env
