open import Function
open import Algebra.FunctionProperties.Core

open import LinearAlgebra.Scalar

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; compare; equal; less; greater)
open import Data.Vec
  using ( _∷_; []; replicate; map; foldr; zipWith; tabulate)
  renaming (Vec to BaseVec)

--------------------------------------------------------------------------
-- Traditional n-dimensional vector

module LinearAlgebra.Vec
  {c} (scalar : Scalar c)
  where

open Scalar scalar
  using ()
  renaming ( Carrier to S
           ; 0# to s0 ; 1# to s1 ; -1# to s-1
           ; _+_ to s+
           ; _*_ to s*
           ; -_ to s- )

-- `Vec n' is the type of n-dimensional vectors of Scalar elements

Vec : ℕ → Set c
Vec = BaseVec S

-- Vector operators:

module _ {n} where

  -- zero vector
  v0 : Vec n
  v0 = replicate s0

  -- pairwise sum
  _+_ : Op₂ (Vec n)
  _+_ = zipWith s+

  -- scalar mul
  _*_ : S → Vec n → Vec n
  k * u = map (s* k) u

  -- negation
  negate : Op₁ (Vec n)
  negate = s-1 *_

  -- dot product
  _·_ : Vec n → Vec n → S
  v · u = foldr _ s+ s0 (zipWith s* v u)

-- essential vector (e.g. column in identity matrix)
essential : ∀ {n} → Fin n → Vec n
essential Fin.zero    = s1 ∷ v0
essential (Fin.suc i) = s0 ∷ essential i
