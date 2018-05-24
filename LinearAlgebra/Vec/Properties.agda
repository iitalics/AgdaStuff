open import Level using (Level; _⊔_)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Algebra.FunctionProperties
open import Algebra.Structures

open import LinearAlgebra

open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (_∷_; []; replicate; zipWith; map; foldr)

import Data.Vec.Properties as VecP

--------------------------------------------------------------------------
-- Properties of n-dimensional vectors

module LinearAlgebra.Vec.Properties
  {c} (scalar : Scalar c)
  where

  open import LinearAlgebra.Vec scalar

  open Scalar scalar
    using ()
    renaming ( Carrier to S
             ; 0# to s0 ; 1# to s1
             ; _+_ to _s+_
             ; _*_ to _s*_
             ; +-identity to s+-identity
             ; +-inverse to s+-inverse
             ; +-assoc to s+-assoc
             ; *-identity to s*-identity
             ; *-zero to s*-zero
             ; distrib to s*+-distrib
             )

  -- Properties of vector _+_

  +-assoc : ∀ {n} → Associative _≡_ (_+_ {n})
  +-assoc [] [] [] = PE.refl
  +-assoc (x ∷ w) (y ∷ v) (z ∷ u) = PE.cong₂ _∷_ (s+-assoc x y z) (+-assoc w v u)

  +-identityˡ : ∀ {n} → LeftIdentity _≡_ v0 (_+_ {n})
  +-identityʳ : ∀ {n} → RightIdentity _≡_ v0 (_+_ {n})
  +-identityˡ v rewrite VecP.zipWith-replicate₁ _s+_ s0 v
    = PE.trans (VecP.map-cong (proj₁ s+-identity) v) (VecP.map-id v)
  +-identityʳ v rewrite VecP.zipWith-replicate₂ _s+_ v s0
    = PE.trans (VecP.map-cong (proj₂ s+-identity) v) (VecP.map-id v)

  +-inverseˡ : ∀ {n} → LeftInverse _≡_ v0 (negate {n}) _+_
  +-inverseʳ : ∀ {n} → RightInverse _≡_ v0 (negate {n}) _+_
  +-inverseˡ [] = PE.refl
  +-inverseˡ (x ∷ xs) = PE.cong₂ _∷_ (proj₁ s+-inverse x) (+-inverseˡ xs)
  +-inverseʳ [] = PE.refl
  +-inverseʳ (x ∷ xs) = PE.cong₂ _∷_ (proj₂ s+-inverse x) (+-inverseʳ xs)

  -- Properties of scalar _*_

  *-identityˡ : ∀ {n} (v : Vec n) → s1 * v ≡ v
  *-identityˡ v rewrite VecP.map-cong (proj₁ s*-identity) v = VecP.map-id v

  *-zeroˡ : ∀ {n} (v : Vec n) → s0 * v ≡ v0
  *-zeroˡ [] = PE.refl
  *-zeroˡ (x ∷ v) = PE.cong₂ _∷_ (proj₁ s*-zero x) (*-zeroˡ v)

  -- Properties of _*_ and _+_

  *+-distribˡ : ∀ {n} (k : S) (v u : Vec n) → k * (v + u) ≡ (k * v) + (k * u)
  *+-distribˡ k [] [] = PE.refl
  *+-distribˡ k (x ∷ v) (y ∷ u) = PE.cong₂ _∷_ (proj₁ s*+-distrib k x y) (*+-distribˡ k v u)
  *+-distribʳ : ∀ {n} (k j : S) (v : Vec n) → (k s+ j) * v ≡ (k * v) + (j * v)
  *+-distribʳ k j [] = PE.refl
  *+-distribʳ k j (x ∷ v) = PE.cong₂ _∷_ (proj₂ s*+-distrib x k j) (*+-distribʳ k j v)

  -- Algebra structures

  +-isSemigroup : ∀ n → IsSemigroup (_≡_ {A = Vec n}) _+_
  +-isSemigroup n = record
    { isEquivalence = PE.isEquivalence
    ; assoc = +-assoc
    ; ∙-cong = PE.cong₂ _ }

  +-isMonoid : ∀ n → IsMonoid (_≡_ {A = Vec n}) _+_ v0
  +-isMonoid n = record
    { isSemigroup = +-isSemigroup n
    ; identity = +-identityˡ , +-identityʳ }

  +-isGroup : ∀ n → IsGroup (_≡_ {A = Vec n}) _+_ v0 negate
  +-isGroup n = record
    { isMonoid = +-isMonoid n
    ; inverse = +-inverseˡ , +-inverseʳ
    ; ⁻¹-cong = PE.cong _ }

  isVectorSpace : ∀ n → IsVectorSpace scalar {V = Vec n} _+_ v0 negate _*_
  isVectorSpace n = record
    { vectorIsGroup = +-isGroup n
    ; distribˡ = *+-distribˡ
    ; distribʳ = *+-distribʳ
    ; *-identityˡ = *-identityˡ
    ; *-zeroˡ = *-zeroˡ }

  vectorSpace : ∀ n → VectorSpace _ _
  vectorSpace n = record { isVectorSpace = isVectorSpace n }
