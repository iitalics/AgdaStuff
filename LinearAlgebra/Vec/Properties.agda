open import Level using (Level; _⊔_)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Algebra.FunctionProperties
open import Algebra.Structures

open import LinearAlgebra

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (_∷_; []; replicate; zipWith; map; foldr; lookup)
open import Data.Product using (_,_; proj₁; proj₂)

import Data.Vec.Properties as VecP

open PE.≡-Reasoning

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
             ; +-assoc to s+-assoc
             ; +-isCommutativeMonoid to s+-isComMonoid
             ; *-identity to s*-identity
             ; *-assoc to s*-assoc
             ; *-comm to s*-comm
             ; -1*-inverse to s-1*-inverse
             ; zero to s*-zero
             ; distrib to s*+-distrib )

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
  +-inverseˡ (x ∷ xs) = PE.cong₂ _∷_ (proj₁ s-1*-inverse x) (+-inverseˡ xs)
  +-inverseʳ [] = PE.refl
  +-inverseʳ (x ∷ xs) = PE.cong₂ _∷_ (proj₂ s-1*-inverse x) (+-inverseʳ xs)

  -- Properties of scalar _*_

  *-identityˡ : ∀ {n} (v : Vec n) → s1 * v ≡ v
  *-identityˡ v rewrite VecP.map-cong (proj₁ s*-identity) v = VecP.map-id v

  *-assoc : ∀ {n} (k j : S) (v : Vec n) → (k s* j) * v ≡ k * (j * v)
  *-assoc k j [] = PE.refl
  *-assoc k j (x ∷ v) = PE.cong₂ _∷_ (s*-assoc k j x) (*-assoc k j v)

  zeroˡ : ∀ {n} (v : Vec n) → s0 * v ≡ v0
  zeroˡ [] = PE.refl
  zeroˡ (x ∷ v) = PE.cong₂ _∷_ (proj₁ s*-zero x) (zeroˡ v)

  -- Properties of _*_ and _+_

  distribˡ : ∀ {n} (k : S) (v u : Vec n) → k * (v + u) ≡ (k * v) + (k * u)
  distribʳ : ∀ {n} (k j : S) (v : Vec n) → (k s+ j) * v ≡ (k * v) + (j * v)
  distribˡ k [] [] = PE.refl
  distribˡ k (x ∷ v) (y ∷ u) = PE.cong₂ _∷_ (proj₁ s*+-distrib k x y) (distribˡ k v u)
  distribʳ k j [] = PE.refl
  distribʳ k j (x ∷ v) = PE.cong₂ _∷_ (proj₂ s*+-distrib x k j) (distribʳ k j v)

  -- Properties of scalar _·_

  ·-comm : ∀ {n} (v u : Vec n) → (v · u) ≡ (u · v)
  ·-comm [] [] = PE.refl
  ·-comm (x ∷ v) (y ∷ u) = PE.cong₂ _s+_ (s*-comm x y) (·-comm v u)

  ·-assoc : ∀ {n} (k : S) (v u : Vec n) → (k * v) · u ≡ k s* (v · u)
  ·-assoc k [] [] = PE.sym $ proj₂ s*-zero k
  ·-assoc k (x ∷ v) (y ∷ u) = begin
      (k * (x ∷ v)) · (y ∷ u)           ≡⟨⟩
      ((k s* x) s* y) s+ ((k * v) · u)  ≡⟨ PE.cong₂ _s+_ (s*-assoc k x y) (·-assoc k v u) ⟩
      (k s* (x s* y)) s+ (k s* (v · u)) ≡⟨ PE.sym (proj₁ s*+-distrib k _ _) ⟩
      k s* ((x ∷ v) · (y ∷ u)) ∎

  ·-distribˡ : ∀ {n} (w v u : Vec n) → w · (v + u) ≡ (w · v) s+ (w · u)
  ·-distribˡ [] [] [] = PE.sym $ proj₁ s+-identity s0
  ·-distribˡ (x ∷ w) (y ∷ v) (z ∷ u)
    rewrite
      proj₁ s*+-distrib x y z
    | ·-distribˡ w v u
    = solve 4 (λ y z v u →
        (y ⊕ z) ⊕ (v ⊕ u)
          ⊜
        (y ⊕ v) ⊕ (z ⊕ u))
      PE.refl (x s* y) (x s* z) (w · v) (w · u)
    where
      open import Algebra.CommutativeMonoidSolver
        (record { isCommutativeMonoid = s+-isComMonoid })

  ·-distribʳ : ∀ {n} (w v u : Vec n) → (v + u) · w ≡ (v · w) s+ (u · w)
  ·-distribʳ w v u = begin
      (v + u) · w         ≡⟨ ·-comm (v + u) w ⟩
      w · (v + u)         ≡⟨ ·-distribˡ w v u ⟩
      (w · v) s+ (w · u)  ≡⟨ PE.cong₂ _s+_ (·-comm w v) (·-comm w u) ⟩
      (v · w) s+ (u · w) ∎

  ·-zeroʳ : ∀ {n} (v : Vec n) → (v · v0) ≡ s0
  ·-zeroʳ [] = PE.refl
  ·-zeroʳ (x ∷ v) = begin
      (x s* s0) s+ (v · v0) ≡⟨ PE.cong₂ _s+_ (proj₂ s*-zero x) (·-zeroʳ v) ⟩
      s0 s+ s0              ≡⟨ proj₁ s+-identity s0 ⟩
      s0 ∎

  ·-zeroˡ : ∀ {n} (v : Vec n) → (v0 · v) ≡ s0
  ·-zeroˡ v rewrite ·-comm v0 v = ·-zeroʳ v

  -- Properties of essential

  essential-lookup : ∀ {n} (i : Fin n) (v : Vec n) → v · essential i ≡ lookup i v
  essential-lookup Fin.zero (x ∷ v)
    rewrite PE.cong₂ _s+_ (proj₂ s*-identity x) (·-zeroʳ v)
    = proj₂ s+-identity x
  essential-lookup (Fin.suc i) (x ∷ v) =
    let recur = v · essential i in
    begin
      (x s* s0) s+ recur ≡⟨ PE.cong (_s+ recur) (proj₂ s*-zero x) ⟩
      s0 s+ recur        ≡⟨ proj₁ s+-identity recur ⟩
      recur              ≡⟨ essential-lookup i v ⟩
      lookup i v ∎

  -- Algebra structures

  module _ (n : ℕ) where

    +-isSemigroup : IsSemigroup (_≡_ {A = Vec n}) _+_
    +-isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = +-assoc
      ; ∙-cong = PE.cong₂ _ }

    +-isMonoid : IsMonoid _≡_ _+_ v0
    +-isMonoid = record
      { isSemigroup = +-isSemigroup
      ; identity = +-identityˡ , +-identityʳ }

    +-isGroup : IsGroup _≡_ _+_ v0 negate
    +-isGroup = record
      { isMonoid = +-isMonoid
      ; inverse = +-inverseˡ , +-inverseʳ
      ; ⁻¹-cong = PE.cong _ }

    isVectorSpace : IsVectorSpace scalar _+_ v0 _*_
    isVectorSpace = record
      { +-isGroup = +-isGroup
      ; *-identityˡ = *-identityˡ
      ; *-assoc = *-assoc
      ; distribˡ = distribˡ
      ; distribʳ = distribʳ
      ; zeroˡ = zeroˡ }

    vectorSpace : VectorSpace _ _
    vectorSpace = record { isVectorSpace = isVectorSpace }

    vectorSpaceOver : VectorSpaceOver scalar _
    vectorSpaceOver = record { isVectorSpace = isVectorSpace }
