module PoriTT.Eval where

import DeBruijn (Ctx)

data VTerm (ctx :: Ctx)
type role VTerm nominal
instance Show (VTerm ctx)

data VElim (ctx :: Ctx)
type role VElim nominal
instance Show (VElim ctx)
