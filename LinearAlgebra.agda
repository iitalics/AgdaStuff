open import Level using (suc; _⊔_)
open import Algebra.FunctionProperties.Core

module LinearAlgebra where

open import LinearAlgebra.Structures public
open import LinearAlgebra.Scalar public

-- Vector space

record VectorSpace c₁ c₂ : Set (suc (c₁ ⊔ c₂)) where
  field
    scalar : Scalar c₁
    V : Set c₂
    _+_ : Op₂ V
    v0 : V
    negate : Op₁ V
    _*_ : Scalar.Carrier scalar → V → V
    isVectorSpace : IsVectorSpace scalar _+_ v0 negate _*_

  open IsVectorSpace isVectorSpace public

  open Scalar scalar public
    using ()
    renaming (Carrier to S)
