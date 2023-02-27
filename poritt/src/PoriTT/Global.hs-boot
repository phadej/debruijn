module PoriTT.Global where

import PoriTT.PP

-- We need this hs-boot file to have globals (which contain values) in terms.

data Global
instance Show Global

prettyGlobal :: Global -> Doc
