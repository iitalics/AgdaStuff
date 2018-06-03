open import Level using (_⊔_)
open import Function
open import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Relation.Unary as U using (Pred; Universal)
open PE.≡-Reasoning

open import Data.Unit using (⊤; tt)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Vec
  using (foldr; zipWith; map; replicate; tabulate)
  renaming (Vec to BaseVec)

open import LinearAlgebra

import Data.Vec.Properties as BaseVecP
import LinearAlgebra.Matrix.Lemmas as Lemmas

------------------------------------------------------------------------

module LinearAlgebra.Subspace.Properties
  {s} {scalar : Scalar s}
  where

open Scalar scalar
  using ()
  renaming ( Carrier to S ; 0# to s0 ; 1# to s1
           ; _+_ to _s+_ ; _*_ to _s*_ )

------------------------------------------------------------------------

module Any
  {c} (space : VectorSpaceOver scalar c)
  where

  open VectorSpaceOver space
    using ( V ; _+_ ; _*_ ; v0
          ; +-identity
          ; zeroˡ
          ; zeroʳ )

  open import LinearAlgebra.Subspace space
  import LinearAlgebra.Vec scalar as Vec
  open Vec.Combination space

  import LinearAlgebra.Vec.CombinationProperties space as CombP

  -------------------------------------------------------
  -- The origin is a subspace

  origin-isSubspace : IsSubspace Origin
  origin-isSubspace = record
    { origin = PE.refl
    ; sum = λ { PE.refl PE.refl → PE.sym (proj₁ +-identity v0) }
    ; scale = λ { k PE.refl → PE.sym (zeroʳ k) } }

  -------------------------------------------------------
  -- All universal sets are subspaces

  U→isSubspace : ∀ {c′} {𝕍 : Pred V c′}
    → Universal 𝕍
    → IsSubspace 𝕍
  U→isSubspace univ = record
    { origin = univ v0
    ; sum = λ _ _ → univ _
    ; scale = λ _ _ → univ _ }

  -------------------------------------------------------
  -- Spans form subspaces

  span-isSubspace : ∀ {n} {vs : BaseVec V n}
    → IsSubspace (Span vs)
  span-isSubspace {n} {vs} = record
    { origin =
      PE.subst (Span vs) (CombP.zero-combination vs)
        $ span (replicate s0)
    ; sum = λ { (span as) (span bs) →
      PE.subst (Span vs) (CombP.+-combine as bs vs)
        $ span (zipWith _s+_ as bs) }
    ; scale = λ { k (span as) →
      PE.subst (Span vs) (CombP.*-combine k as vs)
        $ span (map (k s*_) as) } }

------------------------------------------------------------------------

open Any
