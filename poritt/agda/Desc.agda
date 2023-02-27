module Desc where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

-------------------------------------------------------------------------------
-- Descriptions
-------------------------------------------------------------------------------

data Desc : Set₁ where
  `1 : Desc
  `Σ : (S : Set) (D : S → Desc) → Desc
  `X : Desc -> Desc
  `H : (H : Set) (D : Desc) -> Desc

-- Induction
indDesc : ∀ {ℓ}
  → (M : Desc → Set ℓ)
  → (1ₘ : M `1)
  → (Σₘ : (S : Set) (D : S → Desc) → ((s : S) → M (D s)) → M (`Σ S D))
  → (Xₘ : (D : Desc) -> M D -> M (`X D))
  → (Hₘ : (H : Set) (D : Desc) → M D → M (`H H D))
  → (d : Desc)
  → M d
indDesc M 1ₘ Σₘ Xₘ Hₘ `1       = 1ₘ
indDesc M 1ₘ Σₘ Xₘ Hₘ (`Σ S D) = Σₘ S D (λ s → indDesc M 1ₘ Σₘ Xₘ Hₘ (D s))
indDesc M 1ₘ Σₘ Xₘ Hₘ (`X D)   = Xₘ D (indDesc M 1ₘ Σₘ Xₘ Hₘ D)
indDesc M 1ₘ Σₘ Xₘ Hₘ (`H H D) = Hₘ H D (indDesc M 1ₘ Σₘ Xₘ Hₘ D)

-- evalDesc
⟦_⟧ : Desc → Set → Set
⟦ `1     ⟧ X = ⊤
⟦ `Σ S D ⟧ X = Σ S λ s → ⟦ D s ⟧ X
⟦ `X D   ⟧ X = X × ⟦ D ⟧ X
⟦ `H H D ⟧ X = ((h : H) → X) × ⟦ D ⟧ X

evalDesc : Desc → Set → Set
evalDesc = ⟦_⟧

⟦_⟧' : Desc → Set → Set
⟦ D ⟧' = indDesc
  (λ _ → Set → Set)
  (λ _ → ⊤)
  (λ S _ F X → Σ S λ s → F s X)
  (λ D F X → X × F X)
  (λ H D F X → ((h : H) → X) × F X)
  D

⟦_⟧'' : Desc → Set → Set
⟦ D ⟧'' X = indDesc
  (λ _ → Set)
  ⊤
  (λ S _ F → Σ S λ s → F s)
  (λ D F → X × F)
  (λ H D F → ((h : H) → X) × F)
  D

module Check where

  import Axiom.Extensionality.Propositional as Axiom
  open import Level

  module _ (funExt : Axiom.Extensionality 0ℓ (suc 0ℓ)) where
    evalCheck : (D : Desc) (X : Set) → (⟦ D ⟧ X) ≡ (⟦ D ⟧' X)
    evalCheck `1       X = refl
    evalCheck (`Σ S D) X = cong (Σ S)       (funExt λ s → evalCheck (D s) X)
    evalCheck (`X D)   X = cong (Σ X)       (funExt λ x → evalCheck D X)
    evalCheck (`H H D) X = cong (Σ (H → X)) (funExt λ x → evalCheck D X)

All : (D : Desc) (X : Set) (P : X → Set) → (xs : ⟦ D ⟧ X) → Set
All `1       X P tt      = ⊤
All (`Σ S D) X P (s , d) = All (D s) X P d
All (`X D)   X P (x , d) = P x × All D X P d
All (`H H D) X P (f , d) = ((h : H) → P (f h)) × All D X P d

All' : (D : Desc)     (X : Set) (P : X → Set) → (xs : ⟦ D ⟧' X) → Set
All' = indDesc (λ D → (X : Set) (P : X → Set) (xs : ⟦ D ⟧' X) → Set)
  (λ           X P _  → ⊤)
  (λ S D Dₘ    X P xs → Dₘ (xs .proj₁) X P (xs .proj₂))
  (λ D Dₘ      X P xs → P (xs .proj₁) × Dₘ X P (xs .proj₂))
  (λ H D Dₘ    X P xs → ((h : H) → P (xs .proj₁ h)) × Dₘ X P (xs .proj₂))

All'' : (D : Desc) (X : Set) (P : X → Set) → (xs : ⟦ D ⟧'' X) → Set
All'' D X P = indDesc (λ D → ⟦ D ⟧'' X → Set)
  (λ        _  → ⊤)
  (λ S D Dₘ xs → Dₘ (xs .proj₁) (xs .proj₂)  )
  (λ D Dₘ   xs → P (xs .proj₁) × Dₘ (xs .proj₂))
  (λ H D Dₘ xs → ((h : H) → P (xs .proj₁ h)) × Dₘ (xs .proj₂))
  D

all : (D : Desc)      (X : Set) (P : X → Set) (p : (x : X) → P x) → (xs : ⟦ D ⟧ X) → All D X P xs
all `1       X P p tt      = tt
all (`Σ S D) X P p (s , d) = all (D s) X P p d
all (`X D)   X P p (x , d) = p x , all D X P p d
all (`H H D) X P p (f , d) = (λ h → p (f h)) , all D X P p d

all' : (D : Desc)     (X : Set) (P : X → Set) (p : (x : X) → P x) → (xs : ⟦ D ⟧' X) → All' D X P xs
all' = indDesc (λ D → (X : Set) (P : X → Set) (p : (x : X) → P x) → (xs : ⟦ D ⟧' X) → All' D X P xs)
  (λ          X P p xs → tt)
  (λ S D allD X P p xs → allD (xs .proj₁) X P p (xs .proj₂))
  (λ D allD   X P p xs → p (xs .proj₁) , allD X P p (xs .proj₂))
  (λ H D allD X P p xs → (λ h → p (xs .proj₁ h)) , allD X P p (xs .proj₂))

all'' : (D : Desc) (X : Set) (P : X → Set) (p : (x : X) → P x) → (xs : ⟦ D ⟧'' X) → All'' D X P xs
all'' D X P p = indDesc (λ D →                                   (xs : ⟦ D ⟧'' X) → All'' D X P xs)
  (λ          xs → tt)
  (λ S D allD xs → allD (xs .proj₁) (xs .proj₂))
  (λ D   allD xs → p (xs .proj₁) , allD (xs .proj₂))
  (λ H D allD xs → (λ h → p (xs .proj₁ h)) , allD (xs .proj₂))
  D

-------------------------------------------------------------------------------
-- Fixed point
-------------------------------------------------------------------------------

data μ (D : Desc) : Set where
  con : ⟦ D ⟧ (μ D) → μ D

{-# TERMINATING #-} -- Silly agda
-- D is implicit.
ind : {D : Desc}
    → (x : μ D)
    → (M : μ D → Set)
    → (conₘ : (d : ⟦ D ⟧ (μ D)) → All D (μ D) M d → M (con d))
    →  M x
ind {D} (con d) M conₘ = conₘ d (all D (μ D) M (λ x → ind x M conₘ) d)

-------------------------------------------------------------------------------
-- catamorphism
-------------------------------------------------------------------------------

replace : (D : Desc) (X Y : Set) (d : ⟦ D ⟧ X) → All D X (λ _ → Y) d → ⟦ D ⟧ Y
replace `1       X Y d       a       = tt
replace (`Σ S D) X Y (s , d) a       = s , replace (D s) X Y d a
replace (`X D)   X Y (x , d) (y , a) = y , replace D X Y d a
replace (`H H D) X Y (f , d) (g , a) = g , replace D X Y d a

replace' : (D : Desc) (X Y : Set) (d : ⟦ D ⟧ X) → All D X (λ _ → Y) d → ⟦ D ⟧ Y
replace' D X Y = indDesc (λ D → (d : ⟦ D ⟧ X) → All D X (λ _ → Y) d → ⟦ D ⟧ Y)
  (λ D _           → tt)
  (λ S D rec xs ys → xs .proj₁ , rec (xs .proj₁) (xs .proj₂) ys)
  (λ D   rec xs ys → ys .proj₁ , rec (xs .proj₂) (ys .proj₂))
  (λ H D rec xs ys → ys .proj₁ , rec (xs .proj₂) (ys .proj₂))
  D

cata : {D : Desc}
     → (x : μ D)
     → (T : Set)
     → (⟦ D ⟧ T → T)
     → T
cata {D} x T f = ind x (λ _ → T) λ d d' → f (replace D (μ D) T d d')

-------------------------------------------------------------------------------
-- Natural numbers
-------------------------------------------------------------------------------

-- 1. Type of constructors: {:zero :succ}
data NatC : Set where
  zero : NatC
  succ : NatC

indNatC : ∀ {ℓ} (e : NatC) (M : NatC → Set ℓ) → M zero → M succ → M e
indNatC zero M Mzero Msucc = Mzero
indNatC succ M Mzero Msucc = Msucc

caseNatC : ∀ {ℓ} {A : Set ℓ} → NatC → A → A → A
caseNatC {A = A} e = indNatC e (λ _ → A)

-- 2. Definition of fields
NatF : NatC → Desc
NatF c = caseNatC c `1 (`X `1)

NatD : Desc
NatD = `Σ NatC NatF

check₁ : ⟦ NatD ⟧ ⊤ ≡ Σ NatC (λ s → ⟦ caseNatC s `1 (`X `1) ⟧ ⊤)
check₁ = refl

check₂ : ⟦ NatD ⟧' ⊤ ≡ Σ NatC (λ s → ⟦ caseNatC s `1 (`X `1) ⟧' ⊤)
check₂ = refl

Nat : Set
Nat = μ NatD

zeroₖ : Nat
zeroₖ = con (zero , tt)

succₖ : Nat → Nat
succₖ n = con (succ , n , tt)

IndNat : Set₁
IndNat = (M : Nat → Set)
       → (zeroₘ : M zeroₖ)
       → (succₘ : (n : Nat) → M n → M (succₖ n))
       → (e : Nat)
       → M e

indΣ : ∀ {A : Set} {B : A → Set} (e : Σ A B) (M : Σ A B → Set) (m : (x : A) (y : B x) → M (x , y)) → M e
indΣ e M m = m (e .proj₁) (e .proj₂)

-- indNat defined using Agda's pattern matching
indNat' : IndNat
indNat' M zeroₘ succₘ e = ind e M λ where
  (zero , tt)     tt        → zeroₘ
  (succ , n , tt) (Mn , tt) → succₘ n Mn

-- indNat defined using inductions
indNat : IndNat
indNat M zeroₘ succₘ e =
  ind e M λ d →
  indΣ {A = NatC} {B = λ s → ⟦ NatF s ⟧ Nat} d (λ d' → All (NatF (proj₁ d')) Nat M (proj₂ d') → M (con d')) λ c →
  indNatC c (λ c' → (y : evalDesc (NatF c') Nat) → All (NatF c') Nat M y → M (con (c' , y)))
    (λ _ _ → zeroₘ)
    (λ n Mn → succₘ (n .proj₁) (Mn .proj₁))
