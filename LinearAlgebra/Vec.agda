open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Algebra.FunctionProperties.Core
open import Algebra.Structures

open import Data.Nat using (ℕ)
open import Data.Vec
  using ( _∷_; []
        ; tabulate; map; foldr; zipWith)
  renaming (Vec to BaseVec)

--------------------------------------------------------------------------
-- Traditional n-dimensional vector

module LinearAlgebra.Vec
  {c} {Scalar : Set c}
  {_s+_ _s*_ : Op₂ Scalar}
  {s0 s1 : Scalar}
  (scalarIsSemiring : IsSemiring _≡_ _s+_ _s*_ s0 s1)
  where

  -- `Vec n' is the type of n-dimensional vectors of Scalar elements

  Vec : ℕ → Set c
  Vec = BaseVec Scalar

  -- Vector operators:

  v0 : ∀ {n} → Vec n
  v0 = tabulate (const s0)

  _+_ : ∀ {n} → Op₂ (Vec n)
  _+_ = zipWith _s+_

  _*_ : ∀ {n} → Scalar → Vec n → Vec n
  k * u = map (_s*_ k) u

  _·_ : ∀ {n} → Vec n → Vec n → Scalar
  v · u = foldr _ _s+_ s0 (zipWith _s*_ v u)
