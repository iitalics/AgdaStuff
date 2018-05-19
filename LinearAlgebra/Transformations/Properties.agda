open import Level using (Level; _⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import LinearAlgebra.Structures

module LinearAlgebra.Transformations.Properties
  where

  module One
    {c₁ c₂} {S : Set c₁} {V : Set c₂}
    {_s+_ _s*_ : Op₂ S}
    {_+_ : Op₂ V} {_*_ : S → V → V}
    {s0 s1 : S} {v0 : V}
    (isVecSp : IsVectorSpaceWithoutDot _s+_ _s*_ _+_ _*_ s0 s1 v0)
    where

    open IsVectorSpaceWithoutDot isVecSp
      using ( *+-distribˡ )

    open import LinearAlgebra.Transformations _+_ _*_ _+_ _*_

    id-isLinear : IsLinearFn id
    id-isLinear = record
      { scale = λ _ _ → PE.refl
      ; sum   = λ _ _ → PE.refl }

    identity : LinearFn
    identity = record { isLinearFn = id-isLinear }

    scale-isLinear : ∀ k → IsLinearFn (_*_ k)
    scale-isLinear k = record
      { scale = λ j v → {!!}
      ; sum = *+-distribˡ k }
