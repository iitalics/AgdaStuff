open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality using (_≡_)

module LinearAlgebra.Transformations.Core where

LinearScale : ∀ {s a b} {S : Set s} {A : Set a} {B : Set b}
  (*₁ : S → A → A) (*₂ : S → B → B)
  → (A → B) → Set _
LinearScale _*₁_ _*₂_ f = ∀ k v → (f (k *₁ v) ≡ k *₂ (f v))

LinearSum : ∀ {a b} {A : Set a} {B : Set b}
  (+₁ : Op₂ A) (+₂ : Op₂ B)
  → (A → B) → Set _
LinearSum _+₁_ _+₂_ f = ∀ v u → (f (v +₁ u) ≡ f v +₂ f u)
