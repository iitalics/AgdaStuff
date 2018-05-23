open import Level using (Level; _⊔_)
open import Algebra.Structures
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module LinearAlgebra.Structures where

--------------------------------------------------------------------------
-- Scalars

record IsScalar
    {c} {S : Set c}
    (_s+_ _s*_ : Op₂ S)
    (s0 s1 : S)
    : Set c where
  field
    isCommutativeSemiring : IsCommutativeSemiring _≡_ _s+_ _s*_ s0 s1

  open IsCommutativeSemiring isCommutativeSemiring public

--------------------------------------------------------------------------
-- Vector spaces without dot product

record IsVectorSpace
    {c₁ c₂} {S : Set c₁} {V : Set c₂}
    (_s+_ _s*_ : Op₂ S)
    (_+_ : Op₂ V) (_*_ : S → V → V)
    (s0 s1 : S) (v0 : V)
    : Set (c₁ ⊔ c₂) where
  field
    scalarIsScalar : IsScalar _s+_ _s*_ s0 s1
    vectorIsMonoid : IsMonoid _≡_ _+_ v0
    distribˡ : ∀ k v u → k * (v + u) ≡ (k * v) + (k * u)
    *-identityˡ : ∀ u → s1 * u ≡ u
    *-zeroˡ     : ∀ u → s0 * u ≡ v0
    *-zeroʳ     : ∀ k → k * v0 ≡ v0

  open IsScalar scalarIsScalar public
    using ()
    renaming ( +-assoc to s+-assoc
             ; +-comm to s+-comm
             ; +-identity to s+-identity
             ; *-assoc to s*-assoc
             ; *-comm to s*-comm
             ; *-identity to s*-identity
             ; zero to s*-zero )

  open IsMonoid vectorIsMonoid public
    using ()
    renaming ( assoc to +-assoc
             ; identity to +-identity )
