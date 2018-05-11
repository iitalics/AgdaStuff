open import Level using (Level; _⊔_)
open import Algebra.Structures
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Vec using (Vec; _∷_; []; foldr; zipWith)
open import LinearAlgebra.Structures

module LinearAlgebra where

-- Vector space without dot product

record VectorSpaceWithoutDot c₁ c₂ : Set (Level.suc (c₁ ⊔ c₂)) where
  field
    Scalar : Set c₁
    Vector : Set c₂
    _s+_ _s*_ : Op₂ Scalar
    _+_ : Op₂ Vector
    _*_ : Scalar → Vector → Vector
    s0 s1 : Scalar
    v0 : Vector
    isVectorSpaceWithoutDot : IsVectorSpaceWithoutDot _s+_ _s*_ _+_ _*_ s0 s1 v0

  open IsVectorSpaceWithoutDot isVectorSpaceWithoutDot public

-- Vector space

record VectorSpace c₁ c₂ : Set (Level.suc (c₁ ⊔ c₂)) where
  field
    Scalar : Set c₁
    Vector : Set c₂
    _s+_ _s*_ : Op₂ Scalar
    _+_ : Op₂ Vector
    _*_ : Scalar → Vector → Vector
    _·_ : Vector → Vector → Scalar
    s0 s1 : Scalar
    v0 : Vector
    isVectorSpace : IsVectorSpace _s+_ _s*_ _+_ _*_ _·_ s0 s1 v0

  open IsVectorSpace isVectorSpace public

  vectorSpaceWithoutDot : VectorSpaceWithoutDot _ _
  vectorSpaceWithoutDot = record { isVectorSpaceWithoutDot = isVectorSpaceWithoutDot }
