{-# LANGUAGE StrictData #-}
module PoriTT.Raw (
    Raw (..),
    rapp,
    rapps,
    rsel,
    unRLoc,
    prettyRaw,
    ToRaw (..),
) where

import qualified Data.Map as Map

import PoriTT.Base
import PoriTT.Loc
import PoriTT.Name
import PoriTT.PP

import {-# SOURCE #-} PoriTT.Global (Global, prettyGlobal)

-- | Raw syntax.
type Raw :: Type
data Raw where
    -- | type: @U@
    RUni :: Raw

    -- | variable: @x@
    RVar :: Name -> Raw

    -- | global variable: @g@ (not produced by parser)
    RGbl :: Global -> Raw

    -- | function abstraction: @\\x -> t@
    RLam :: Name -> Raw -> Raw
    -- | dependent function type: @forall (x : T) -> S@
    RPie :: Name -> Raw -> Raw -> Raw
    -- | function type: @T -> S@
    RArr :: Raw -> Raw -> Raw

    -- | function application: @f t s ...@.
    -- Also selectors, e.g.: @f t .fst s .snd@
    RApp :: Raw -> [Either Selector Raw] -> Raw

    -- | sigma type: @exists (x : T) * S@
    RSgm :: Name -> Raw -> Raw -> Raw
    -- | product type: @T * S@
    RPrd :: Raw -> Raw -> Raw
    -- | pair constructor: @t , s@
    RMul :: Raw -> Raw -> Raw

    -- | finite set type: @{:true :false}@
    RFin :: Set Label -> Raw
    -- | label: @:true@
    RLbl :: Label -> Raw
    -- | switch case: @switch e { :true -> t; :false -> s }@
    RSwh :: Raw -> Raw -> Map Label Raw -> Raw

    -- | descriptions' type: @Desc@
    RDsc :: Raw
    -- | unit description: @`1@
    RDe1 :: Raw
    -- | sigma description: @`S S D@
    RDeS :: Raw -> Raw -> Raw
    -- | index description: @`X D@
    RDeX :: Raw -> Raw
    -- | description induction: @indDesc d m case1 caseS caseX@
    RDeI :: Raw -> Raw -> Raw -> Raw -> Raw -> Raw

    -- | Fixed-point of descriptions: @mu t@
    RMuu :: Raw -> Raw
    -- | Fixed-point wrap: @con t@
    RCon :: Raw -> Raw
    -- | Fixed-point induction: @ind e M f@
    RInd :: Raw -> Raw -> Raw -> Raw

    -- | Code: @Code t@
    RCod :: Raw -> Raw
    -- | Quote: @<t>@
    RQuo :: Raw -> Raw
    -- | Splice: ~t
    RSpl :: Raw -> Raw

    -- | type annotation: @t : T@
    RAnn :: Raw -> Raw -> Raw
    -- | let binding: @let x : t = s in e@ or @let x = f in e@
    RLet :: Name -> Raw -> Raw -> Raw
    -- | hole: @_@
    RHol :: Raw
    -- | source location
    RLoc :: Loc -> Raw -> Raw
  deriving Show

unRLoc :: Raw -> Raw
unRLoc (RLoc _ r) = unRLoc r
unRLoc r          = r

-- | Function application
rapp :: Raw -> Raw -> Raw
rapp (RApp f ts) t = RApp f (ts ++ [Right t])
rapp f           t = RApp f [Right t]

rapps :: Raw -> [Raw] -> Raw
rapps = foldl' rapp

-- | Selector application
rsel :: Raw -> Selector -> Raw
rsel (RApp f ts) s = RApp f (ts ++ [Left s])
rsel f           s = RApp f [Left s]

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

-- | Class for conversion of scoped things into raw syntax.
--
-- We implement pretty-printing for raw syntax only, to not repeat ourselves.
class ToRaw t where
    toRaw :: NameScope -> Env ctx Name -> t ctx -> Raw

-- precedences
appp, annp, funp, sgmp, comp, keyp, splp :: Int
splp = 11 --
appp = 10 -- left
sgmp = 5  -- right
funp = 4  -- right
comp = 3  -- right
annp = 1  -- right
keyp = 0  -- none

prettyRaw :: Int -> Raw -> Doc
prettyRaw d (RLoc _ r)       = prettyRaw d r
prettyRaw d (RLam x t)       = ppParensIf (d > keyp) $ prettyLam ("\\" <+> prettyName x) t
prettyRaw d (RSwh e m ts)    = ppParensIf (d > keyp) $ ("switch" <+> prettyRaw (appp + 1) e <+> prettyRaw (appp + 1) m) <//> pbraceSemi
    [ prettyLabel l <+> ppSyArr <+> prettyRaw 0 t
    | (l, t) <- Map.toList ts
    ]
prettyRaw d (RLet x t s)     = ppParensIf (d > keyp) $ "let" <+> prettyName x <+> "=" <+> prettyRaw 0 t <+> "in" <+> prettyRaw 0 s
prettyRaw d (RArr a b)       = ppParensIf (d > funp) $ prettyRaw (funp + 1) a <+> ppTyArr </> prettyRaw funp b
prettyRaw d (RPie x a b)     = ppParensIf (d > funp) $ prettyPie (ppParens (prettyName x <+> ":" <+> prettyRaw 0 a) :) b
prettyRaw d (RPrd a b)       = ppParensIf (d > sgmp) $ prettyRaw (sgmp + 1) a <+> "*" </> prettyRaw sgmp b
prettyRaw d (RSgm x a b)     = ppParensIf (d > sgmp) $ prettySgm (ppParens (prettyName x <+> ":" <+> prettyRaw 0 a) :) b
prettyRaw d (RAnn t s)       = ppParensIf (d > annp) $ prettyRaw (annp + 1) t <//> ":" <+> prettyRaw annp s
prettyRaw d (RMul t s)       = ppParensIf (d > comp) $ prettyRaw (comp + 1) t <+> "," <+> prettyRaw comp s
prettyRaw d (RApp f [])      = prettyRaw d f
prettyRaw d (RApp f ts)      = ppParensIf (d > appp) $ prettyApp (prettyRaw appp f) (map (either prettySelector $ prettyRaw (appp + 1)) ts)
prettyRaw _ (RFin ls)        = prettyLabels ls
prettyRaw _ (RLbl l)         = prettyLabel l
prettyRaw _ (RVar x)         = prettyName x
prettyRaw _ (RGbl g)         = prettyGlobal g
prettyRaw d (RMuu t)         = ppParensIf (d > appp) $ "mu" <+> prettyRaw (appp + 1) t
prettyRaw d (RCon t)         = ppParensIf (d > appp) $ "con" <+> prettyRaw (appp + 1) t
prettyRaw d (RInd e m c)     = ppParensIf (d > appp) $ prettyApp "ind" (map (prettyRaw 11) [e,m,c])
prettyRaw _ RDsc             = "Desc"
prettyRaw _ RDe1             = "`1"
prettyRaw d (RDeS s t)       = ppParensIf (d > appp) $ "`S" <+> prettyRaw (appp + 1) s <+> prettyRaw (appp + 1) t
prettyRaw d (RDeX t)         = ppParensIf (d > appp) $ "`X" <+> prettyRaw (appp + 1) t
prettyRaw d (RDeI e m x y z) = ppParensIf (d > appp) $ prettyApp "indDesc" (map (prettyRaw (appp +1)) [e,m,x,y,z])
prettyRaw d (RCod a)         = ppParensIf (d > appp) $ prettyApp "Code" [prettyRaw (appp + 1) a]
prettyRaw _ (RQuo t)         = ppQuote $ prettyRaw 0 t
prettyRaw d (RSpl t)         = ppParensIf (d > splp) $ "$" <> prettyRaw (splp + 1) t
prettyRaw _ RUni             = "U"
prettyRaw _ RHol             = "_"

prettyApp :: Doc -> [Doc] -> Doc
prettyApp f xs = ppSoftHanging f xs

prettyPie :: ([Doc] -> [Doc]) -> Raw -> Doc
prettyPie acc (RPie x a b) = prettyPie (acc . (ppParens (prettyName x <+> ":" <+> prettyRaw 0 a) :)) b
prettyPie acc b            = "forall" <//> ppSep (acc []) <+> ppTyArr </> prettyRaw funp b

prettySgm :: ([Doc] -> [Doc]) -> Raw -> Doc
prettySgm acc (RSgm x a b) = prettySgm (acc . (ppParens (prettyName x <+> ":" <+> prettyRaw 0 a) :))  b
prettySgm acc b            = "exists" <//> ppSep (acc []) <+> "*" </> prettyRaw sgmp b

prettyLam :: Doc -> Raw -> Doc
prettyLam acc (RLam x t) = prettyLam (acc <+> prettyName x) t
prettyLam acc t          = (acc <+> ppSyArr) <//> prettyRaw keyp t
