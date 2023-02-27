module PoriTT.Opts where

data Opts = Opts
    { optsEvalFull :: !Bool  -- ^ Evaluate the terms fully
    , optsEcho     :: !Bool  -- ^ Echo the poritt statements
    }
  deriving Show

defaultOpts :: Opts
defaultOpts = Opts
    { optsEvalFull = False
    , optsEcho     = True
    }
