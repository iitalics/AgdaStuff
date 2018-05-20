import Level
open import Function
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary as B using (Rel)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Data.Nat using (ℕ; suc; _+_; _*_; pred; _≤_; _≤?_; _≟_)
open import Data.Product using (_,_; ,_; ∃; proj₁)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import Data.Vec using (_[_]≔_; lookup)
import Data.Star
import Data.Star.Properties

open import Imperative.Base

module Imperative.Semantics where

------------------------------------------------------------------------
-- Semantics of expressions

⟦_⟧e : ∀ {n} → Ex n → Env n → V
⟦ cst c ⟧e ρ = c
⟦ var x ⟧e ρ = lookup x ρ
⟦ e +′ e₁ ⟧e ρ = ⟦ e ⟧e ρ + ⟦ e₁ ⟧e ρ
⟦ e *′ e₁ ⟧e ρ = ⟦ e ⟧e ρ * ⟦ e₁ ⟧e ρ
⟦ 1+ e ⟧e ρ = suc (⟦ e ⟧e ρ)
⟦ 1- e ⟧e ρ = pred (⟦ e ⟧e ρ)

⟦_⟧P : ∀ {n} → Pr n → Pred (Env n) _
⟦ z? e ⟧P ρ = 0 ≡ ⟦ e ⟧e ρ
⟦ nz? e ⟧P ρ = 1 ≤ ⟦ e ⟧e ρ
⟦ e₁ =′ e₂ ⟧P ρ = ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
⟦ e₁ ≤′ e₂ ⟧P ρ = ⟦ e₁ ⟧e ρ ≤ ⟦ e₂ ⟧e ρ

⟦_⟧p : ∀ {n} (p : Pr n) → U.Decidable ⟦ p ⟧P
⟦ z? e ⟧p ρ = 0 ≟ ⟦ e ⟧e ρ
⟦ nz? e ⟧p ρ = 1 ≤? ⟦ e ⟧e ρ
⟦ e₁ =′ e₂ ⟧p ρ = ⟦ e₁ ⟧e ρ ≟ ⟦ e₂ ⟧e ρ
⟦ e₁ ≤′ e₂ ⟧p ρ = ⟦ e₁ ⟧e ρ ≤? ⟦ e₂ ⟧e ρ

------------------------------------------------------------------------
-- Machine state

record M (n : ℕ) : Set where
  constructor ⟨_,_⟩
  field
    ρ : Env n    -- memory
    s : St n     -- program counter

-- predicates about statements

data IsNoOp {n} : Pred (St n) Level.zero where
  is-no-op : IsNoOp no-op

is-no-op? : ∀ {n} → U.Decidable (IsNoOp {n})
is-no-op? (x ≔ e) = no λ ()
is-no-op? (s ⟫ s₁) = no λ ()
is-no-op? (while p s) = no λ ()
is-no-op? no-op = yes is-no-op

data CanStep {n} : Pred (M n) Level.zero where
  can-step : ∀ {ρ s} → ¬ IsNoOp s → CanStep ⟨ ρ , s ⟩

------------------------------------------------------------------------
-- Small-step semantics

data _═>_ {n : ℕ} : Rel (M n) Level.zero where
  put : ∀ {x ρ e}
    → let ρ′ = ρ [ x ]≔ ⟦ e ⟧e ρ in
      ⟨ ρ , x ≔ e ⟩ ═> ⟨ ρ′ , no-op ⟩

  skip : ∀ {ρ s}
    → ⟨ ρ , no-op ⟫ s ⟩ ═> ⟨ ρ , s ⟩

  cont : ∀ {ρ ρ′ s s′ s₂}
    → ⟨ ρ , s ⟩ ═> ⟨ ρ′ , s′ ⟩
    → ⟨ ρ , s ⟫ s₂ ⟩ ═> ⟨ ρ′ , s′ ⟫ s₂ ⟩

  while1 : ∀ {ρ p s}
    → ⟦ p ⟧P ρ
    → ⟨ ρ , while p s ⟩ ═> ⟨ ρ , s ⟫ while p s ⟩

  while0 : ∀ {ρ p s}
    → ¬ ⟦ p ⟧P ρ
    → ⟨ ρ , while p s ⟩ ═> ⟨ ρ , no-op ⟩

-- Small step is decidable iff "CanStep m" (a.k.a. not a no-op)
step : ∀ {n} (m : M n) {_ : CanStep m} → ∃ (_═>_ m)
step ⟨ ρ , x ≔ e ⟩ = , put
step ⟨ ρ , s ⟫ s₂ ⟩ with is-no-op? s
... | yes is-no-op = , skip
... | no ¬no-op with step (⟨ ρ , s ⟩) {can-step ¬no-op}
...   | _ , m⇒m′ = , cont m⇒m′
step ⟨ ρ , while p s ⟩ with ⟦ p ⟧p ρ
... | yes tru = , while1 tru
... | no fals = , while0 fals
step ⟨ ρ , no-op ⟩ {can-step f} = ⊥-elim (f is-no-op)

------------------------------------------------------------------------
-- Large-step (transitive closure)

_─>_ : ∀ {n} → Rel (M n) _
_─>_ = Data.Star.Star _═>_

module StepReasoning n =
  Data.Star.Properties.StarReasoning (_═>_ {n})
