open import Level using (suc; _⊔_)
open import Algebra.FunctionProperties.Core

open import LinearAlgebra.Structures

module LinearAlgebra where

-- Vector space

record VectorSpace c₁ c₂ : Set (suc (c₁ ⊔ c₂)) where
  field
    Scalar : Set c₁
    Vector : Set c₂
    _s+_ _s*_ : Op₂ Scalar
    _+_ : Op₂ Vector
    _*_ : Scalar → Vector → Vector
    s0 s1 : Scalar
    v0 : Vector
    isVectorSpace : IsVectorSpace _s+_ _s*_ _+_ _*_ s0 s1 v0

  open IsVectorSpace isVectorSpace public
