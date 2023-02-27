module Eta where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- eta for Unit
ex1 : (x y : ⊤) → x ≡ y
ex1 _ _ = refl

-- product of units
ex2 : (x y : ⊤ × ⊤) → x ≡ y
ex2 _ _ = refl

-- function to unit
ex3 : (x y : Set → ⊤) → x ≡ y
ex3 _ _ = refl

