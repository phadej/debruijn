{-# LANGUAGE Safe #-}
module DeBruijn.RenExtras (
    weakenUsingSize,
) where

import DeBruijn.Ctx
import DeBruijn.Ren
import DeBruijn.Size
import DeBruijn.Wk

-- | Weaken closed term to arbitrary context.
--
-- Note: this has different requirements than 'sinkSize'.
weakenUsingSize :: Rename t => Size ctx -> t EmptyCtx -> t ctx
weakenUsingSize s0 = weaken (go s0) where
    go :: Size ctx -> Wk EmptyCtx ctx
    go SZ     = IdWk
    go (SS s) = SkipWk (go s)
