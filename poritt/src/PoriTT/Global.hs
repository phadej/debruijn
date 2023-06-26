module PoriTT.Global (
    Global (..),
    prettyGlobal,
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.PP
import PoriTT.Term
import PoriTT.Value (VElim, VTerm)

data Global = Global
    { gblName   :: !Name
    , gblTerm   :: Elim EmptyCtx
    , gblType   :: VTerm EmptyCtx
    , gblVal    :: VElim EmptyCtx
    , gblInline :: Bool
    }
  deriving Show

prettyGlobal :: Global -> Doc
prettyGlobal = ppAnnotate AGbl . prettyName . gblName
