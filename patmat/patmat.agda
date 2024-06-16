module patmat where

open import Data.List using (List; []; _∷_)
open import Data.NP
open import Data.Idx

data Ty : Set where
  foo : Ty
  bar : Ty
  fun : Ty → Ty → Ty

Ctx = List Ty

variable
  A B C D E : Ty
  Γ Δ Ω Ψ Φ : Ctx

data Expr (Γ : Ctx) : Ty → Set
data Alt (Γ : Ctx) (C : Ty) : Ty → Set

data Expr Γ where
  var : Idx A Γ → Expr Γ A
  lam : Expr (A ∷ Γ) B → Expr Γ (fun A B)
  app : Expr Γ (fun A B) → Expr Γ A → Expr Γ B
  mch : Expr Γ A → List (Alt Γ C A) → Expr Γ C

data Alt Γ C where
  varA : Expr (A ∷ Γ) C → Alt Γ C A
  fooA : Expr (bar ∷ bar ∷ Γ) C → Alt Γ C foo

-- Pat A Γ Δ matches on a value of type A and extends Γ to Δ
data Pat : Ty → Ctx → Ctx → Set where
  varP : Pat A Γ (A ∷ Γ)
  fooP : Pat bar Γ (bar ∷ Γ) → Pat bar (bar ∷ Γ) (bar ∷ bar ∷ Γ) → Pat foo Γ (bar ∷ bar ∷ Γ)

data Path {A : Set} (p : A → A → Set) (x : A) : A → Set where
    refl : Path p x x
    _∷_  : {y : A} → p x y → {z : A} → Path p y z → Path p x z

-- ClauseN Γ Δ A is clauses defined in context Γ with prefix of types Δ results of type A
data ClauseN : Ctx → Ctx → Ty → Set where

data Pats : Ctx → Ctx → Ctx → Ctx → Set where
     [] : Pats Γ Γ Ω Ω
     _∷_ : Pat A Ω Ψ → Pats (A ∷ Γ) Δ Ψ Φ → Pats Γ Δ Ω Φ

ex : ∀ {Γ} → Pats Γ (foo ∷ foo ∷ Γ) Γ (bar ∷ bar ∷ bar ∷ bar ∷ Γ)
ex = fooP varP varP ∷ fooP varP varP ∷ []
