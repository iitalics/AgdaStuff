open import Level using (Level; _⊔_)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Algebra.FunctionProperties
open import Algebra.Structures

open import LinearAlgebra.Structures

open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
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

  open IsSemiring scalarIsSemiring
    using ()
    renaming ( +-assoc to s+-assoc
             ; +-identity to s+-identity
             ; *-identity to s*-identity
             ; zero to s*-zero
             ; distrib to s*+-distrib )

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

  -------------------------------------------

  module Properties where

    -- Properties of +

    +-assoc : ∀ {n} → Associative _≡_ (_+_ {n})
    +-assoc [] [] [] = PE.refl
    +-assoc (x ∷ w) (y ∷ v) (z ∷ u) = PE.cong₂ _∷_ (s+-assoc x y z) (+-assoc w v u)

    +-identityˡ : ∀ {n} → LeftIdentity _≡_ v0 (_+_ {n})
    +-identityʳ : ∀ {n} → RightIdentity _≡_ v0 (_+_ {n})
    +-identityˡ [] = PE.refl
    +-identityˡ (x ∷ v) = PE.cong₂ _∷_ (proj₁ s+-identity x) (+-identityˡ v)
    +-identityʳ [] = PE.refl
    +-identityʳ (x ∷ v) = PE.cong₂ _∷_ (proj₂ s+-identity x) (+-identityʳ v)


    -- Properties of _*_

    *-zeroˡ : ∀ {n} (v : Vec n) → s0 * v ≡ v0
    *-zeroˡ [] = PE.refl
    *-zeroˡ (x ∷ v) rewrite *-zeroˡ v | proj₁ s*-zero x = PE.refl

    *-zeroʳ : ∀ n (k : Scalar) → k * (v0 {n}) ≡ v0
    *-zeroʳ zero k = PE.refl
    *-zeroʳ (suc n) k = PE.cong₂ _∷_ (proj₂ s*-zero k) (*-zeroʳ n k)

    *-identityˡ : ∀ {n} (v : Vec n) → s1 * v ≡ v
    *-identityˡ [] = PE.refl
    *-identityˡ (x ∷ v) = PE.cong₂ _∷_ (proj₁ s*-identity x) (*-identityˡ v)


    -- Properties of _*_ and _+_

    *+-distribˡ : ∀ {n} (k : Scalar) (v u : Vec n) → k * (v + u) ≡ (k * v) + (k * u)
    *+-distribˡ k [] [] = PE.refl
    *+-distribˡ k (x ∷ v) (y ∷ u) = PE.cong₂ _∷_ (proj₁ s*+-distrib k x y) (*+-distribˡ k v u)


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

    isVectorSpaceWithoutDot : ∀ n →
      IsVectorSpaceWithoutDot Scalar (Vec n) _s+_ _s*_ _+_ _*_ s0 s1 v0
    isVectorSpaceWithoutDot n = record
      { scalarIsSemiring = scalarIsSemiring
      ; vectorIsMonoid = +-isMonoid n
      ; *+-distribˡ = *+-distribˡ
      ; *-identityˡ = *-identityˡ
      ; *-zeroˡ = *-zeroˡ
      ; *-zeroʳ = *-zeroʳ n }
