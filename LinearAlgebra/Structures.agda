open import Level using (Level; _⊔_)
open import Algebra.Structures
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Unary using (Pred) renaming (Decidable to UDec)

open PE.≡-Reasoning
open import Data.Product using (proj₁; proj₂)

open import LinearAlgebra.Scalar

module LinearAlgebra.Structures where

--------------------------------------------------------------------------
-- Vector spaces without dot product

record IsVectorSpace
    {c₁} (scalar : Scalar c₁)
    {c₂} {V : Set c₂} (_+_ : Op₂ V) (v0 : V)
    (_*_ : Scalar.Carrier scalar → V → V)
    : Set (c₁ ⊔ c₂) where

  open Scalar scalar public
    using ()
    renaming ( Carrier to S
             ; _+_ to _s+_
             ; -_ to s-
             ; _*_ to _s*_
             ; _⁻¹ to s⁻¹
             ; 0# to s0 ; 1# to s1
             ; +-assoc to s+-assoc
             ; +-comm to s+-comm
             ; +-identity to s+-identity
             ; *-assoc to s*-assoc
             ; *-comm to s*-comm
             ; *-identity to s*-identity )

  s-1 : S
  s-1 = s- s1

  negate : Op₁ V
  negate v = s-1 * v

  _-_ : Op₂ V
  v - u = v + negate u

  field
    +-isGroup : IsGroup _≡_ _+_ v0 negate
    *-identityˡ : ∀ u → s1 * u ≡ u
    *-assoc : ∀ j k v → (j s* k) * v ≡ j * (k * v)
    distribˡ : ∀ k v u → k * (v + u) ≡ (k * v) + (k * u)
    distribʳ : ∀ j k v → (j s+ k) * v ≡ (j * v) + (k * v)
    zeroˡ : ∀ u → s0 * u ≡ v0
    zeroʳ : ∀ k → k * v0 ≡ v0

  open IsGroup +-isGroup public
    using ()
    renaming ( assoc to +-assoc
             ; identity to +-identity
             ; inverse to +-inverse )

  cancels→zero : ∀ w
    → (w + w ≡ w)
    → w ≡ v0
  cancels→zero w 2w=w = begin
    w              ≡⟨ PE.sym (proj₂ +-identity w) ⟩
    w + v0         ≡⟨ PE.cong (w +_) (PE.sym (proj₂ +-inverse w)) ⟩
    w + (w - w)    ≡⟨ PE.sym (+-assoc w w (negate w)) ⟩
    (w + w) - w    ≡⟨ PE.cong (_- w) 2w=w ⟩
    w - w          ≡⟨ proj₂ +-inverse w ⟩
    v0 ∎
