open import Level using (Level; _⊔_)
open import Function
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≢_)
open import Data.Product using (∃; _,_; proj₁; proj₂)

module LinearAlgebra.Scalar where

-- Values not equal to some value (for instance, zero)

NotEqual : ∀ {c} {A : Set c} (x : A) → Set c
NotEqual x = ∃ (_≢_ x)

-- Scalar fields

record IsScalar
  {c} {S : Set c}
  (_+_ : Op₂ S) (-_ : Op₁ S) (0# : S)
  (_*_ : Op₂ S) (_⁻¹ : Op₁ (NotEqual 0#)) (1# : S)
  : Set c where

  field
    isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ 0# 1#
    *-inverseʳ : ∀ a → proj₁ a * proj₁ (a ⁻¹) ≡ 1#

  open IsCommutativeRing isCommutativeRing public
    using ( +-identity
          ; +-assoc
          ; -‿inverse
          ; +-comm
          ; +-isGroup
          ; +-isMonoid
          ; *-identity
          ; *-assoc
          ; *-comm
          ; *-isMonoid
          ; zero
          ; distrib )

  *-inverseˡ : ∀ a → proj₁ (a ⁻¹) * proj₁ a ≡ 1#
  *-inverseˡ (x , x≠0) =
    begin
      (_ * x) ≡⟨ *-comm _ _ ⟩
      (x * _) ≡⟨ *-inverseʳ _ ⟩
      1# ∎
    where open PE.≡-Reasoning

-- Scalar type

record Scalar c : Set (Level.suc c) where
  field
    Carrier : Set c
    _+_ _*_ : Op₂ Carrier
    0# 1# : Carrier
    -_ : Op₁ Carrier
    _⁻¹ : Op₁ (NotEqual 0#)
    isScalar : IsScalar _+_ -_ 0# _*_ _⁻¹ 1#

  open IsScalar isScalar public