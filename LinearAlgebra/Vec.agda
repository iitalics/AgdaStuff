open import Function
open import Algebra.FunctionProperties.Core

open import LinearAlgebra.Scalar

open import Data.Nat using (ℕ)
open import Data.Vec
  using ( _∷_; []; replicate; map; foldr; zipWith)
  renaming (Vec to BaseVec)

--------------------------------------------------------------------------
-- Traditional n-dimensional vector

module LinearAlgebra.Vec
  {c} (scalar : Scalar c)
  where

  open Scalar scalar
    using ()
    renaming ( Carrier to S
             ; 0# to s0 ; -1# to s-1
             ; _+_ to s+
             ; _*_ to s*
             ; -_ to s- )

  -- `Vec n' is the type of n-dimensional vectors of Scalar elements

  Vec : ℕ → Set c
  Vec = BaseVec S

  -- Vector operators:

  module _ {n} where

    v0 : Vec n
    v0 = replicate s0

    _+_ : Op₂ (Vec n)
    _+_ = zipWith s+

    _*_ : S → Vec n → Vec n
    k * u = map (s* k) u

    negate : Op₁ (Vec n)
    negate = s-1 *_

    _·_ : Vec n → Vec n → S
    v · u = foldr _ s+ s0 (zipWith s* v u)
