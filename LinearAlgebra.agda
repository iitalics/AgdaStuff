open import Level using (suc; _⊔_)
open import Algebra.FunctionProperties.Core

module LinearAlgebra where

open import LinearAlgebra.Structures public
open import LinearAlgebra.Scalar public

-- Vector space over a scalar

record VectorSpaceOver
  {c₁} (scalar : Scalar c₁) c₂
  : Set (c₁ ⊔ suc c₂) where
  field
    V : Set c₂
    _+_ : Op₂ V
    _*_ : Scalar.Carrier scalar → V → V
    v0 : V
    isVectorSpace : IsVectorSpace scalar _+_ v0 _*_

  open Scalar scalar public
    using ()
    renaming (Carrier to S)

  open IsVectorSpace isVectorSpace public

-- Vector space (with scalar existentially qualified)

record VectorSpace c₁ c₂ : Set (suc (c₁ ⊔ c₂)) where
  field
    scalar : Scalar c₁
    V : Set c₂
    _+_ : Op₂ V
    _*_ : Scalar.Carrier scalar → V → V
    v0 : V
    isVectorSpace : IsVectorSpace scalar _+_ v0 _*_

  open IsVectorSpace isVectorSpace public

  open Scalar scalar public
    using ()
    renaming (Carrier to S)

  vectorSpaceOver : VectorSpaceOver scalar c₂
  vectorSpaceOver = record { isVectorSpace = isVectorSpace }
