open import Level using (Level; _⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import LinearAlgebra
import LinearAlgebra.Transformations

module LinearAlgebra.Transformations.Properties
  where

  module One
    {c₁ c₂} (vectorSpace : VectorSpace c₁ c₂)
    where

    open VectorSpace vectorSpace
    open LinearAlgebra.Transformations _+_ _*_ _+_ _*_

    id-is-linear : IsLinearFn id
    id-is-linear = record
      { scale = λ _ _ → PE.refl
      ; sum = λ _ _ → PE.refl }

    scale-is-linear : ∀ k → IsLinearFn (k *_)
    scale-is-linear k = record
      { scale = λ j v → begin
          k * (j * v)    ≡⟨ PE.sym $ *-assoc k j v ⟩
          (k s* j) * v   ≡⟨ PE.cong (_* v) (s*-comm k j) ⟩
          (j s* k) * v   ≡⟨ *-assoc j k v ⟩
          j * (k * v) ∎
      ; sum = distribˡ k }
      where
        open PE.≡-Reasoning

    negate-is-linear : IsLinearFn negate
    negate-is-linear = scale-is-linear s-1

    ∘-is-linear : ∀ {f g}
      → IsLinearFn f
      → IsLinearFn g
      → IsLinearFn (f ∘ g)
    ∘-is-linear {f} {g} f-lin g-lin = record
      { scale = λ k v → begin
          f (g (k * v))   ≡⟨ PE.cong f (IsLinearFn.scale g-lin k v) ⟩
          f (k * g v)     ≡⟨ IsLinearFn.scale f-lin k (g v) ⟩
          k * f (g v) ∎
      ; sum = λ v u → begin
          f (g (v + u))   ≡⟨ PE.cong f (IsLinearFn.sum g-lin v u) ⟩
          f (g v + g u)   ≡⟨ IsLinearFn.sum f-lin (g v) (g u) ⟩
          f (g v) + f (g u) ∎ }
      where
        open PE.≡-Reasoning
