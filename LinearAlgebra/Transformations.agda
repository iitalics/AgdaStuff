open import Level using (Level; _⊔_)
open import Function
open import Function.Inverse using (_↔_)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import LinearAlgebra
open import LinearAlgebra.Transformations.Core

module LinearAlgebra.Transformations
    {s c₁ c₂} {scalar : Scalar s}
    (space₁ : VectorSpaceOver scalar c₁)
    (space₂ : VectorSpaceOver scalar c₂)
    where

  open VectorSpaceOver space₁
    using (V; v0)
    renaming (_+_ to _v+_ ; _*_ to _v*_ )

  open VectorSpaceOver space₂
    using ()
    renaming (V to U ; v0 to u0 ; _+_ to _u+_ ; _*_ to _u*_)

  --------------------------------------------------
  -- Linear functions

  record IsLinearFn (f : V → U) : Set (s ⊔ c₁ ⊔ c₂) where
    field
      scale : LinearScale _v*_ _u*_ f
      sum : LinearSum _v+_ _u+_ f

  record LinearFn : Set (Level.suc (s ⊔ c₁ ⊔ c₂)) where
    field
      apply : V → U
      isLinearFn : IsLinearFn apply

  --------------------------------------------------
  -- Kernels

  record Kernel (f : V → U) (v : V) : Set c₂ where
    field
      prop : f v ≡ u0

  IsTrivial : ∀ {a} → Pred (Pred V a) _
  IsTrivial P = ∀ v → (P v ↔ v ≡ v0)
