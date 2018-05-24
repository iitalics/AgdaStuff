open import Level using (Level; _⊔_)
open import Algebra.Structures
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Unary using (Pred) renaming (Decidable to UDec)

open import LinearAlgebra.Scalar

module LinearAlgebra.Structures where

--------------------------------------------------------------------------
-- Vector spaces without dot product

record IsVectorSpace
    {c₁} (scalar : Scalar c₁)
    {c₂} {V : Set c₂} (_+_ : Op₂ V) (negate : V → V) (v0 : V)
    (_*_ : Scalar.Carrier scalar → V → V)
    : Set (c₁ ⊔ c₂) where

  open Scalar scalar public
    using ()
    renaming ( _+_ to _s+_
             ; _*_ to _s*_
             ; 0# to s0 ; 1# to s1
             ; +-assoc to s+-assoc
             ; +-comm to s+-comm
             ; +-identity to s+-identity
             ; *-assoc to s*-assoc
             ; *-comm to s*-comm
             ; *-identity to s*-identity )

  field
    vectorIsGroup : IsGroup _≡_ _+_ v0 negate
    distribˡ : ∀ k v u → k * (v + u) ≡ (k * v) + (k * u)
    distribʳ : ∀ j k v → (j s+ k) * v ≡ (j * v) + (k * v)
    *-identityˡ : ∀ u → s1 * u ≡ u
    *-zeroˡ : ∀ u → s0 * u ≡ v0

  open IsGroup vectorIsGroup public
    using ()
    renaming ( assoc to +-assoc
             ; identity to +-identity
             ; inverse to +-inverse )
