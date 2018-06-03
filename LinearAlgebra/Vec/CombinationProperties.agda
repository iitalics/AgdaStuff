open import Level using (Level; _⊔_)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Algebra.FunctionProperties
open import Algebra.Structures

open import LinearAlgebra

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec
  using (_∷_; []; replicate; zipWith; map; foldr; lookup)
  renaming (Vec to BaseVec)

import Data.Vec.Properties as BaseVecP
import LinearAlgebra.Matrix.Lemmas as Lemmas

open PE.≡-Reasoning

--------------------------------------------------------------------------
-- Properties of linear combinations

module LinearAlgebra.Vec.CombinationProperties
  {s c} {scalar : Scalar s} (space : VectorSpaceOver scalar c)
  where

open Scalar scalar
  using ()
  renaming ( Carrier to S
           ; 0# to s0 ; 1# to s1
           ; _+_ to _s+_
           ; _*_ to _s*_
           )

open VectorSpaceOver space
  using ( V ; _+_ ; _*_ ; v0
        ; +-identity
        ; +-isCommutativeMonoid
        ; *-assoc
        ; distribʳ
        ; distribˡ
        ; zeroˡ
        ; zeroʳ )

open import LinearAlgebra.Subspace space
import LinearAlgebra.Vec scalar as Vec
open Vec.Combination space

zero-combination : ∀ {n}
  → (vs : BaseVec V n)
  → combine (replicate s0) vs ≡ v0
zero-combination [] = PE.refl
zero-combination (v ∷ vs) rewrite
  zeroˡ v | zero-combination vs
  = proj₁ +-identity v0

+-combine : ∀ {n}
  → (as bs : BaseVec S n) (vs : BaseVec V n)
  → combine (zipWith _s+_ as bs) vs ≡ combine as vs + combine bs vs
+-combine [] [] [] = PE.sym (proj₁ +-identity v0)
+-combine (a ∷ as) (b ∷ bs) (v ∷ vs) rewrite
  distribʳ a b v | +-combine as bs vs
  = solve 4 (λ x y X Y →
         (x ⊕ y) ⊕ (X ⊕ Y)
           ⊜
         (x ⊕ X) ⊕ (y ⊕ Y))
       PE.refl
     (a * v) (b * v)
     (combine as vs) (combine bs vs)
  where
    open import Algebra.CommutativeMonoidSolver
      (record { isCommutativeMonoid = +-isCommutativeMonoid })

*-combine : ∀ {n}
  → (k : S) (as : BaseVec S n) (vs : BaseVec V n)
  → combine (map (k s*_) as) vs ≡ k * combine as vs
*-combine k [] [] = PE.sym (zeroʳ k)
*-combine k (a ∷ as) (v ∷ vs) rewrite
  *-assoc k a v | *-combine k as vs
  = PE.sym $ distribˡ k (a * v) (combine as vs)
