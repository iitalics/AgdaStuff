open import Level using (_⊔_; suc)
open import Relation.Unary as U using (Pred; _∈_)
open import Data.Vec using () renaming (Vec to BaseVec)

open import LinearAlgebra

module LinearAlgebra.Subspace
  {s c} {scalar : Scalar s}
  (space : VectorSpaceOver scalar c)
  where

open Scalar scalar
  using ()
  renaming (Carrier to S)

open VectorSpaceOver space
  using (V; _+_; _*_; v0)

import LinearAlgebra.Vec scalar as Vec
open Vec.Combination space

--------------------------------------------------------------------------
-- Subspaces

record IsSubspace {c′} (𝕍 : Pred V c′) : Set (s ⊔ c ⊔ c′) where
  field
    origin : v0 ∈ 𝕍
    sum : ∀ {v w} → v ∈ 𝕍 → w ∈ 𝕍 → (v + w) ∈ 𝕍
    scale : ∀ {v} k → v ∈ 𝕍 → (k * v) ∈ 𝕍

record Subspace c′ : Set (suc (s ⊔ c ⊔ c′)) where
  field
    𝕍 : Pred V c′
    isSubspace : IsSubspace 𝕍

--------------------------------------------------------------------------
-- Vectors in the span of a set of vectors

data Span {n} (vs : BaseVec V n) : Pred V (s ⊔ c) where
  span : (as : BaseVec S n) → combine as vs ∈ Span vs
