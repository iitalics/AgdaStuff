import Function
open import Data.List using (List; []; _∷_)
open import Data.Star using (ε; _◅_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

import Data.Nat.Properties as NatP

module Sorting.Examples where
  open import Sorting.QuickSort
    NatP.≤-isDecTotalOrder

  open import Sorting.Permute

  eg₁ : qsort (5 ∷ 3 ∷ 8 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  eg₂ : qsort (5 ∷ 5 ∷ 4 ∷ 5 ∷ 6 ∷ []) ≡ 4 ∷ 5 ∷ 5 ∷ 5 ∷ 6 ∷ []
  eg₁ = refl
  eg₂ = refl

  eg₃ : (1 ∷ 5 ∷ 3 ∷ []) ≈ₚ (3 ∷ 1 ∷ 5 ∷ [])
  eg₃ = skip swap ◅ swap ◅ ε
