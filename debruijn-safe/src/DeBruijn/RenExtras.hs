{-# LANGUAGE Safe #-}
module DeBruijn.RenExtras (
    weakenSize,
) where

import DeBruijn.Ctx
import DeBruijn.Ren
import DeBruijn.Size
import DeBruijn.Wk

-- | Weaken closed term to arbitrary context.
--
-- Note: this has different requirements than 'sinkSize'.
weakenSize :: Renamable t => Size ctx -> t EmptyCtx -> t ctx
weakenSize s0 = weaken (go s0) where
    go :: Size ctx -> Wk EmptyCtx ctx
    go SZ     = IdWk
    go (SS s) = SkipWk (go s)

