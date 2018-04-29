open import Function
open import Level using () renaming (zero to ℓ₀; suc to ℓsuc)
open import Data.Integer as Int using (ℤ)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_; _≤_; _<_; _<″_)
open import Data.Fin using (Fin; #_; toℕ; raise) renaming (suc to fsuc; zero to fzero)
open import Data.Vec using (Vec; _∷_; []; _++_; head; tail) renaming (lookup to ith)
open import Data.Star using (Star; ε; _◅_; _◅◅_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; sym; trans)
open import Relation.Binary.Core
open import Relation.Unary using (Pred)

import Data.Fin.Properties as FinP
import Data.Nat.Properties as NatP
import Data.Vec.Properties as VecP

module Compiler where
V = ℕ

BinOp = V → V → V
Env = Vec V

Interpreter : ∀ {a} (T : ℕ → Set a) → Set a
Interpreter T = ∀ {w} → T w → Env w → V

{-------------------------------------------------------}
{- Expression (source language) -}
data E (w : ℕ) : Set ℓ₀ where
  lit : V → E w
  var : Fin w → E w
  _<_>_ : E w → BinOp → E w → E w

-- Eval
⟦_⟧ₑ : Interpreter E
⟦ lit c ⟧ₑ ρ = c
⟦ var x ⟧ₑ ρ = ith x ρ
⟦ e₁ < _⊕_ > e₂ ⟧ₑ ρ = ⟦ e₁ ⟧ₑ ρ ⊕ ⟦ e₂ ⟧ₑ ρ

{-------------------------------------------------------}
{- Instructions (target language) -}
data I : Rel ℕ ℓ₀ where
  psh : ∀ {n} → V     → I (0 + n) (1 + n)
  sel : ∀ {n} → Fin n → I (0 + n) (1 + n)
  pop : ∀ {n} → BinOp → I (2 + n) (1 + n)
  swp : ∀ {n}         → I (2 + n) (2 + n)

I* = Star I

Stk = Vec V
StkT : Rel ℕ _
StkT n m = Stk n → Stk m

apply : BinOp → ∀ {n} → StkT (2 + n) (1 + n)
apply _⊕_ (b ∷ a ∷ s) = (a ⊕ b) ∷ s

⟦_⟧ᵢ : I ⇒ StkT
⟦ psh c ⟧ᵢ s = c ∷ s
⟦ sel x ⟧ᵢ s = (ith x s) ∷ s
⟦ pop ⊕ ⟧ᵢ s = apply ⊕ s
⟦ swp ⟧ᵢ   (a ∷ b ∷ s) = b ∷ a ∷ s

⟦_⟧ᵢ⋆ : I* ⇒ StkT
⟦_⟧ᵢ⋆ = Data.Star.foldl StkT (λ f i → ⟦ i ⟧ᵢ ∘ f) id

{-------------------------------------------------------}
{- Full programs (target language) -}
P : ℕ → Set ℓ₀
P w = I* w (1 + w)

-- Run
⟦_⟧ₚ : Interpreter P
⟦ p ⟧ₚ ρ = head (⟦ p ⟧ᵢ⋆ ρ)

{-------------------------------------------------------}
{- Compiler (source -> target) -}

com : ∀ {n} k → E n → I* (k + n) (1 + k + n)
com k (lit c) = psh c ◅ ε
com k (var x) = (sel (raise k x)) ◅ ε
com k (e₁ < ⊕ > e₂) = com k e₁ ◅◅ com (suc k) e₂ ◅◅ pop ⊕ ◅ ε

compile : ∀ {n} → E n → P n
compile = com 0

{-----------}

drop : ∀ {n} k → Stk (k + n) → Stk n
drop zero s = s
drop (suc k) (x ∷ s) = drop k s

take : ∀ {n} k → Stk (k + n) → Stk k
take zero s = []
take (suc k) (x ∷ s) = x ∷ take k s

{-------------------------------------------------------}
module Relations where
  -- equivalent stack transformations
  _≈T_ : ∀ {n m} → Rel (StkT n m) _
  f ≈T g = ∀ s → (f s ≡ g s)

  T-equivalence : ∀ {n m} → IsEquivalence (_≈T_ {n} {m})
  T-equivalence = record
    { refl = λ s → refl
    ; sym = λ f s → sym (f s)
    ; trans = λ f g s → trans (f s) (g s) }

  _≈ᵢ⋆_ : ∀ {n m} → Rel (I* n m) _
  _≈ᵢ⋆_ {n} i* j* = ⟦ i* ⟧ᵢ⋆ ≈T ⟦ j* ⟧ᵢ⋆
