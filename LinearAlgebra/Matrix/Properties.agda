open import Level using (_⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import LinearAlgebra.Scalar

open import Data.Vec
  using ( _∷_; []; map; replicate; zipWith; foldr; tabulate )
  renaming (Vec to BaseVec)

import Data.Vec.Properties as BaseVecP

--------------------------------------------------------------------------
-- Properties of matrices

module LinearAlgebra.Matrix.Properties
  {c} (scalar : Scalar c)
  where

open import LinearAlgebra.Matrix scalar

open Scalar scalar
  using ()
  renaming ( Carrier to S ; 0# to s0 ; -1# to s-1
           ; _+_ to _s+_ ; _*_ to _s*_ ; -_ to s- )

open import LinearAlgebra.Vec scalar
  using ( Vec ; v0 ; essential
        ; _+_ ; _*_ ; _·_ )

import LinearAlgebra.Vec.Properties scalar as VecP

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
-- lemmas

private
  map-on₂ : ∀ {n} {a b c d}
    {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B) (g : A → C) (_*_ : B → C → D)
    (l : BaseVec A n) → map (λ x → f x * g x) l ≡ zipWith _*_ (map f l) (map g l)
  map-on₂ f g _*_ [] = PE.refl
  map-on₂ f g _*_ (x ∷ l) = PE.cong (_ ∷_) $ map-on₂ f g _*_ l

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

module _ {n m} (A : Mat n m) where

  open import LinearAlgebra.Transformations
    (_+_ {m}) _*_
    (_+_ {n}) _*_

  apply-isLinear : IsLinearFn (apply A)
  apply-isLinear = record
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
    where open PE.≡-Reasoning
