open import Level using (_⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≗_)
open import Relation.Binary using (Setoid)

open import LinearAlgebra.Scalar

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec
  using ( _∷_; []; map; replicate; zipWith; foldr; tabulate; lookup; tail)
  renaming (Vec to BaseVec)

import Data.Vec.Properties as BaseVecP
import LinearAlgebra.Matrix.Lemmas as Lemmas

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
import LinearAlgebra.Transformations.Properties as TransformP

------------------------------------------------------------------------
-- Misc. lemmas on transpose and apply

transpose-col : ∀ {n m}
  → (B : Mat n m) (xs : Vec n)
  → transpose (zipWith _∷_ xs B) ≡ xs ∷ transpose B
transpose-col [] [] = PE.refl
transpose-col (row ∷ B) (x ∷ xs) rewrite transpose-col B xs = PE.refl

transpose-flat : ∀ {n}
  → (B : Mat n 0)
  → transpose B ≡ []
transpose-flat [] = PE.refl
transpose-flat ([] ∷ B) rewrite transpose-flat B = PE.refl

apply-col : ∀ {n m}
  → (x : S) (v : Vec m) (C : Vec n) (A : Mat n m)
  → apply (zipWith _∷_ C A) (x ∷ v) ≡ (x * C) + apply A v
apply-col x v [] [] = PE.refl
apply-col x v (_ ∷ C) (_ ∷ A) rewrite apply-col x v C A = PE.refl

------------------------------------------------------------------------
-- Properties of `transpose`

-- Transposing twice yeilds the original matrix

transpose-transpose : ∀ {n m}
  → (A : Mat n m)
  → transpose (transpose A) ≡ A
transpose-transpose {n} = main ∘ cw-view
  where
    open import LinearAlgebra.Matrix.Column-wise scalar
    main : ∀ {m}
      → {B : Mat n m} (cw : Column-wise B)
      → transpose (transpose B) ≡ B
    main []cw rewrite
      transpose-flat {n} (replicate []) = PE.refl
    main (_∷cw_ {A = B} xs cw) rewrite
      transpose-col B xs | main cw = PE.refl

-- Applying the transposed matrix is the linear combination of the rows

apply-transpose : ∀ {n m}
  → (A : Mat n m)
  → apply (transpose A) ≗ flip combine A
apply-transpose [] [] = BaseVecP.map-replicate ([] ·_) _ _
apply-transpose (C ∷ A) (x ∷ v) rewrite
  apply-col x v C (transpose A) | apply-transpose A v = PE.refl

------------------------------------------------------------------------
-- Properties of specific matrices

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
  tabulate (λ i → v · essential i)  ≡⟨ Lemmas.tabulate-cong _ (flip lookup v)
                                        $ flip VecP.essential-lookup v ⟩
  tabulate (flip lookup v)          ≡⟨ BaseVecP.tabulate∘lookup v ⟩
  v ∎

-- the identity is an identity with an additional column and row:
--      [ 1 0 … 0 ]   [ 1 0 0  ]
-- id = | 0 1 … 0 | = [ 0 ⋱ ⋮  |
--      [ 0 0 … 1 ]   [ 0 … id ]
m1-column-row : ∀ k → m1 ≡ essential zero ∷ zipWith _∷_ v0 (m1 {k})
m1-column-row k rewrite
  BaseVecP.tabulate-∘ (s0 ∷_) (essential {k})
  | Lemmas.zipWith-const₁ _∷_ s0 (m1 {k})
  = PE.refl

-- Transposing the identity matrix yeilds the identity matrix

transpose-m1 : ∀ n → transpose m1 ≡ m1 {n}
transpose-m1 0 = PE.refl
transpose-m1 (suc n) = begin
  transpose m1                         ≡⟨ PE.cong transpose (m1-column-row n) ⟩
  transpose (e0 ∷ zipWith _∷_ v0 m1)   ≡⟨ PE.cong (zipWith _∷_ e0) (transpose-col m1 v0) ⟩
  zipWith _∷_ e0 (v0 ∷ transpose m1)   ≡⟨ PE.cong (zipWith _∷_ e0 ∘ (v0 ∷_)) (transpose-m1 n) ⟩
  zipWith _∷_ e0 (v0 ∷ m1)             ≡⟨ PE.sym (m1-column-row n) ⟩
  m1 ∎
  where
    e0 = essential zero

module _ {n m : ℕ} where
  private
    space₁ = VecP.vectorSpaceOver m
    space₂ = VecP.vectorSpaceOver n

  open import LinearAlgebra.Transformations space₁ space₂
    using (IsLinearFn)

  open TransformP.Two space₁ space₂
    using (combine-linear)

  -- Applying a matrix is a linear transformation

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
        map (λ w → (v · w) s+ (u · w)) A  ≡⟨ Lemmas.map-on₂ (v ·_) (u ·_) _s+_ A ⟩
        apply A v + apply A u ∎ }


  -- Unapplying a linear transformation is equivalent to the transformation

  apply-unapply : ∀ T
    → IsLinearFn T
    → apply (unapply T) ≗ T
  apply-unapply T T-lin v = begin
    apply (unapply T) v         ≡⟨ apply-transpose (map T m1) v ⟩
    combine v (map T m1)        ≡⟨ PE.sym (combine-linear T T-lin v m1) ⟩
    T (combine v m1)            ≡⟨ PE.cong T (PE.sym (apply-transpose m1 v)) ⟩
    T (apply (transpose m1) v)  ≡⟨ PE.cong (λ x → T (apply x v)) (transpose-m1 _) ⟩
    T (apply m1 v)              ≡⟨ PE.cong T (m1-identity _ v) ⟩
    T v ∎
