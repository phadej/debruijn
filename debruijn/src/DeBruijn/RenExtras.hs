{-# LANGUAGE Trustworthy #-}
module DeBruijn.RenExtras (
    weakenUsingSize,
) where

import DeBruijn.Ctx
import DeBruijn.Ren
import DeBruijn.Size

import Unsafe.Coerce (unsafeCoerce)

-- | Weaken closed term to arbitrary context.
--
-- Note: this has different requirements than 'sinkSize'.
weakenUsingSize :: Rename t => Size ctx -> t EmptyCtx -> t ctx
weakenUsingSize _ = unsafeCoerce
