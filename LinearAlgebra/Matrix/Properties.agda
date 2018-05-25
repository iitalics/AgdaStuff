open import Level using (_⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≗_)
open import Relation.Binary using (Setoid)

open import LinearAlgebra.Scalar

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec
  using ( _∷_; []; map; replicate; zipWith; foldr; tabulate; lookup)
  renaming (Vec to BaseVec)

import Data.Vec.Properties as BaseVecP

open PE.≡-Reasoning

--------------------------------------------------------------------------
-- Properties of matrices

module LinearAlgebra.Matrix.Properties
  {c} (scalar : Scalar c)
  where

open import LinearAlgebra.Matrix scalar

open Scalar scalar
  using ()
  renaming ( Carrier to S ; 0# to s0 ; 1# to s1 ; -1# to s-1
           ; _+_ to _s+_ ; _*_ to _s*_ ; -_ to s- )

open import LinearAlgebra.Vec scalar
  using ( Vec ; v0 ; essential
        ; _+_ ; _*_ ; _·_ )

import LinearAlgebra.Vec.Properties scalar as VecP

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
-- Lemmas

private
  map-on₂ : ∀ {n} {a b c d}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B) (g : A → C) (_*_ : B → C → D) (l : BaseVec A n)
    → map (λ x → f x * g x) l ≡ zipWith _*_ (map f l) (map g l)
  map-on₂ f g _*_ [] = PE.refl
  map-on₂ f g _*_ (x ∷ l) = PE.cong (_ ∷_) $ map-on₂ f g _*_ l

  tabulate-cong : ∀ {n} {a} {A : Set a}
    (f g : Fin n → A)
    → f ≗ g
    → tabulate f ≡ tabulate g
  tabulate-cong {0}     f g f=g = PE.refl
  tabulate-cong {suc n} f g f=g = PE.cong₂ _∷_ (f=g zero) (tabulate-cong _ _ (f=g ∘ suc))

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

module _ {n m} where

  open import LinearAlgebra.Transformations
    (_+_ {m}) _*_
    (_+_ {n}) _*_

  -- Applying a matrix is a linear operation

  apply-isLinear : ∀ A → IsLinearFn (apply A)
  apply-isLinear A = record
    { scale = λ k v → begin
        apply A (k * v)                   ≡⟨⟩
        map ((k * v) ·_) A                ≡⟨ BaseVecP.map-cong (VecP.·-assoc k v) A ⟩
        map ((k s*_) ∘ (v ·_)) A          ≡⟨ BaseVecP.map-∘ (k s*_) (v ·_) A ⟩
        k * apply A v ∎
    ; sum = λ v u → begin
        apply A (v + u)                   ≡⟨⟩
        map ((v + u) ·_) A                ≡⟨ BaseVecP.map-cong (λ w → VecP.·-distribʳ w v u) A ⟩
        map (λ w → (v · w) s+ (u · w)) A  ≡⟨ map-on₂ (v ·_) (u ·_) _s+_ A ⟩
        apply A v + apply A u ∎ }

-- The zero matrix is a constant transformation

m0-zero : ∀ n m → apply (m0 {n} {m}) ≗ const v0
m0-zero n m v = begin
  apply m0 v                 ≡⟨⟩
  map (v ·_) (replicate v0)  ≡⟨ BaseVecP.map-replicate (v ·_) v0 n ⟩
  replicate (v · v0)         ≡⟨ PE.cong replicate (VecP.·-zeroʳ v) ⟩
  v0 ∎

-- The identity matrix is an identity transformation

m1-identity : ∀ n → apply (m1 {n}) ≗ id
m1-identity n v = begin
  apply m1 v                        ≡⟨⟩
  map (v ·_) (tabulate essential)   ≡⟨ PE.sym $ BaseVecP.tabulate-∘ (v ·_) essential ⟩
  tabulate (λ i → v · essential i)  ≡⟨ tabulate-cong _ (flip lookup v)
                                        (flip VecP.essential-lookup v) ⟩
  tabulate (flip lookup v)          ≡⟨ BaseVecP.tabulate∘lookup v ⟩
  v ∎
