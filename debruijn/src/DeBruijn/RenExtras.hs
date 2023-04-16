{-# LANGUAGE Trustworthy #-}
module DeBruijn.RenExtras (
    weakenSize,
) where

import DeBruijn.Ctx
import DeBruijn.Ren
import DeBruijn.Size

import Unsafe.Coerce (unsafeCoerce)

-- | Weaken closed term to arbitrary context.
--
-- Note: this has different requirements than 'sinkSize'.
weakenSize :: Renamable t => Size ctx -> t EmptyCtx -> t ctx
weakenSize _ = unsafeCoerce
