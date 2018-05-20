open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

module Imperative.Base where

V = ℕ
Env = Vec V

data Ex (n : ℕ) : Set where
  cst       : (c : V) → Ex n
  var       : (x : Fin n) → Ex n
  _+′_ _*′_ : (e₁ e₂ : Ex n) → Ex n
  1+ 1-     : (e : Ex n) → Ex n

data Pr (n : ℕ) : Set where
  z? nz? : (e : Ex n) → Pr n
  _=′_ _≤′_ : (e₁ e₂ : Ex n) → Pr n

data St (n : ℕ) : Set where
 _≔_ : (x : Fin n) (e : Ex n) → St n
 _⟫_ : (s₁ s₂ : St n) → St n
 while : (p : Pr n) (s : St n) → St n
 no-op : St n
