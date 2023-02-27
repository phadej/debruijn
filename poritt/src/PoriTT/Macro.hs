module PoriTT.Macro where

import PoriTT.Well
import PoriTT.Base
import PoriTT.Name

-- | A macro is expanded in renamer.
data Macro where
    Macro :: Name -> Env arity Name -> Well arity -> Macro
