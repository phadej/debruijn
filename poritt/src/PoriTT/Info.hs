module PoriTT.Info (
    infoGlobal,
    infoMacro,
) where

import PoriTT.Base
import PoriTT.Global
import PoriTT.Macro
import PoriTT.Name
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Term
import PoriTT.Well

-------------------------------------------------------------------------------
-- Information about global definition.
-------------------------------------------------------------------------------

infoGlobal :: Global -> Doc
infoGlobal g = ppHanging
    (ppAnnotate ACmd "defined" <+> prettyName (gblName g))
    [ ":" <+> prettyVTerm SZ emptyNameScope EmptyEnv (gblType g)
    , "=" <+> case gblTerm g of
        Ann t _ -> prettyTerm emptyNameScope EmptyEnv 0 t
        e       -> prettyElim emptyNameScope EmptyEnv 0 e
    ]

-------------------------------------------------------------------------------
-- Information about macro
-------------------------------------------------------------------------------

infoMacro :: Macro -> Doc
infoMacro (Macro n xs t) = ppHanging
    (ppAnnotate ACmd "macro" <+> prettyName n <+> ppSep (map prettyName (toList xs)))
    [ "=" <+> prettyWell emptyNameScope xs 0 t
    ]
