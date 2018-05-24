open import Level using (suc; _⊔_)
open import Algebra.FunctionProperties.Core

module LinearAlgebra where

open import LinearAlgebra.Structures public
open import LinearAlgebra.Scalar public

-- Vector space

record VectorSpace c₁ c₂ : Set (suc (c₁ ⊔ c₂)) where
  field
    scalar : Scalar c₁
    Vector : Set c₂
    _+_ : Op₂ Vector
    negate : Vector → Vector
    v0 : Vector
    _*_ : Scalar.Carrier scalar → Vector → Vector
    isVectorSpace : IsVectorSpace scalar _+_ v0 negate _*_

  open IsVectorSpace isVectorSpace public
