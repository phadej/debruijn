-- | Nicer combinators to construct 'Term' and 'Elim's.
module PoriTT.Nice where

import PoriTT.Base
import PoriTT.Name
import PoriTT.Term

-- | Infix function application
(@@) :: FromElim term => Elim ctx -> Term ctx -> term ctx
f @@ x = fromElim (App f x)
infixl 3 @@, .:

-- | Selector
(.:) :: FromElim term => Elim ctx -> Selector -> term ctx
e .: s = fromElim (Sel e s)

-- | Non-dependent function type
(~~>) :: Term ctx -> Term ctx -> Term ctx
a ~~> b = Pie "_" a (weaken wk1 b)
infixr 1 ~~>

-- | Non-dependent pair type
(***) :: Term ctx -> Term ctx -> Term ctx
a *** b = Sgm "_" a (weaken wk1 b)
infixr 2 ***

-- | Nicely embed elims into terms.
class    FromElim term where fromElim :: Elim ctx -> term ctx
instance FromElim Elim where fromElim = id
instance FromElim Term where fromElim = Emb
