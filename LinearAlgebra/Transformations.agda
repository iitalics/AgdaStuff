open import Level using (Level; _⊔_)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Algebra.FunctionProperties.Core
open import Algebra.Structures

open import LinearAlgebra.Structures
open import LinearAlgebra.Transformations.Core

module LinearAlgebra.Transformations
    {s c₁ c₂} {S : Set s} {V : Set c₁} {U : Set c₂}
    (v+ : Op₂ V) (v* : S → V → V)
    (u+ : Op₂ U) (u* : S → U → U)
    where

  --------------------------------------------------
  -- Linear functions

  record IsLinearFn (f : V → U) : Set (s ⊔ c₁ ⊔ c₂) where
    field
      scale : LinearScale v* u* f
      sum : LinearSum v+ u+ f

  record LinearFn : Set (Level.suc (s ⊔ c₁ ⊔ c₂)) where
    field
      apply : V → U
      isLinearFn : IsLinearFn apply
