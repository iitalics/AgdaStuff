open import Level using (_⊔_; suc)
open import Relation.Unary as U using (Pred; _∈_)
open import Data.Vec using () renaming (Vec to BaseVec)

open import LinearAlgebra

module LinearAlgebra.Subspace
  {s c} {scalar : Scalar s}
  (space : VectorSpaceOver scalar c)
  where

open Scalar scalar
  using (-1#)
  renaming (Carrier to S)

open VectorSpaceOver space
  using (V; _+_; _*_; _-_; v0; negate)

import LinearAlgebra.Vec scalar as Vec
open Vec.Combination space

--------------------------------------------------------------------------
-- Subspaces

record IsSubspace {c′} (𝕍 : Pred V c′) : Set (s ⊔ c ⊔ c′) where
  field
    origin : v0 ∈ 𝕍
    sum : ∀ {v w} → v ∈ 𝕍 → w ∈ 𝕍 → (v + w) ∈ 𝕍
    scale : ∀ {v} k → v ∈ 𝕍 → (k * v) ∈ 𝕍

  neg : ∀ {v} → v ∈ 𝕍 → negate v ∈ 𝕍
  neg v∈v = scale -1# v∈v

  sub : ∀ {v w} → v ∈ 𝕍 → w ∈ 𝕍 → (v - w) ∈ 𝕍
  sub v∈v w∈v = sum v∈v (neg w∈v)

record Subspace c′ : Set (suc (s ⊔ c ⊔ c′)) where
  field
    𝕍 : Pred V c′
    isSubspace : IsSubspace 𝕍

--------------------------------------------------------------------------
-- Example predicates

Origin : Pred V _
Origin = U.｛ v0 ｝

--------------------------------------------------------------------------
-- Vectors in the span of a set of vectors

data Span {n} (vs : BaseVec V n) : Pred V (s ⊔ c) where
  span : (as : BaseVec S n) → combine as vs ∈ Span vs
