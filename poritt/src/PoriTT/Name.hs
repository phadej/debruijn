module PoriTT.Name (
    -- * Names
    Name,
    mkName,
    prettyName,
    holeName,
    -- * Selectors
    Selector,
    mkSelector,
    prettySelector,
    -- * Labels
    Label,
    mkLabel,
    prettyLabel,
    prettyLabels,
    -- * Name scope
    NameScope,
    emptyNameScope,
    withFreshName,
    nameScopeFromSet,
    nameScopeMember,
) where

import PoriTT.Base
import PoriTT.PP

import qualified Data.Set        as Set
import qualified Data.Text.Short as ST

-------------------------------------------------------------------------------
-- Name
-------------------------------------------------------------------------------

newtype Name = Name ShortText
  deriving (Eq, Ord)

instance Show Name where
    showsPrec d (Name t) = showsPrec d t

instance IsString Name where
    fromString = Name . fromString

mkName :: Text -> Name
mkName t = Name (ST.fromText t)

prettyName :: Name -> Doc
prettyName (Name t) = ppText (ST.unpack t)

-- | Special name
holeName :: Name
holeName = "_"

-------------------------------------------------------------------------------
-- Selectors and labels
-------------------------------------------------------------------------------

-- | Selectors
newtype Selector = Selector Name
  deriving (Eq, Ord)

instance Show Selector where
    showsPrec d (Selector t) = showsPrec d t

instance IsString Selector where
    fromString = Selector . fromString

-- | Selectors are represented as names (at least for now).
prettySelector :: Selector -> Doc
prettySelector (Selector n) = ppAnnotate ASel ("." <> prettyName n)

mkSelector :: Text -> Selector
mkSelector = coerce mkName

-- | Labels
newtype Label = Label Name
  deriving (Eq, Ord)

instance Show Label where
    showsPrec d (Label t) = showsPrec d t

instance IsString Label where
    fromString = Label . fromString

prettyLabel :: Label -> Doc
prettyLabel (Label n) = ppAnnotate ALbl (":" <> prettyName n)

prettyLabels :: Set Label -> Doc
prettyLabels ls = pbraces (ppSep $ map prettyLabel $ toList ls)

mkLabel :: Text -> Label
mkLabel = coerce mkName

-------------------------------------------------------------------------------
-- NameScope
-------------------------------------------------------------------------------

newtype NameScope = NameScope (Set.Set Name)

instance Semigroup NameScope where
    (<>) = coerce (Set.union @Name)

emptyNameScope :: NameScope
emptyNameScope = NameScope Set.empty

nameScopeFromSet :: Set.Set Name -> NameScope
nameScopeFromSet = NameScope

nameScopeMember :: Name -> NameScope -> Bool
nameScopeMember = coerce (Set.member @Name)

withFreshName :: NameScope -> Name -> (NameScope -> Name -> r) -> r
withFreshName ns              "_" kont = kont ns "_"
withFreshName (NameScope ns0) n0  kont
    | Set.member n0 ns0 = go ns0 n0 (0 :: Int)
    | otherwise         = kont (NameScope (Set.insert n0 ns0)) n0
  where
    go ns n i | Set.member n' ns = go ns n (i + 1)
              | otherwise        = kont (NameScope (Set.insert n' ns)) n'
      where
        n' = case n of Name t -> Name (t <> fromString (show i))
