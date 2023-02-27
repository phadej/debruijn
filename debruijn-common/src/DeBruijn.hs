module DeBruijn (
    -- * Basic building blocks
    -- |
    --
    -- @
    -- data 'Ctx'  :: Kind                   -- contexts
    -- data 'Idx'  :: 'Ctx' -> Type            -- de Bruijn indices
    -- data 'Env'  :: 'Ctx' -> Type -> Type    -- environments
    -- data 'Lvl'  :: 'Ctx' -> Type            -- de Bruijn levels
    -- data 'Size' :: 'Ctx' -> Type            -- context size
    -- @
    --
    module DeBruijn.Ctx,
    module DeBruijn.Idx,
    module DeBruijn.Env,
    module DeBruijn.Lvl,
    module DeBruijn.Size,
    -- * Weakenings, renamings and substitutions
    module DeBruijn.Wk,
    module DeBruijn.Ren,
    module DeBruijn.Sub,
    weakenUsingSize,
    -- * Size addition and less-than-equal predicate
    module DeBruijn.Add,
    -- | Module "DeBruijn.Lte" is not exported,
    -- as it's not that useful in general.
) where

import DeBruijn.Add
import DeBruijn.Ctx
import DeBruijn.Env
import DeBruijn.Idx
import DeBruijn.Lvl
import DeBruijn.Ren
import DeBruijn.RenExtras
import DeBruijn.Size
import DeBruijn.Sub
import DeBruijn.Wk
