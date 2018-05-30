open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Nat using (ℕ)
open import Data.Vec
  using ( _∷_ ; [] ; replicate ; zipWith )
  renaming (Vec to BaseVec)

open import LinearAlgebra.Scalar

open import Data.Vec.Properties as VecP

module LinearAlgebra.Matrix.Column-wise
  {c} (scalar : Scalar c)
  where

open Scalar scalar
  using ()
  renaming ( Carrier to S )

open import LinearAlgebra.Matrix scalar
  using ( Mat )

--------------------------------------------------------------------------
-- Split a matrix by the first column

data Left-col : ∀ {n m} → Mat n (ℕ.suc m) → Set c where
  _∷c_ : ∀ {n m} (xs : BaseVec S n) (A : Mat n m) → Left-col (zipWith _∷_ xs A)

left-col : ∀ {n m} (A : Mat n (ℕ.suc m)) → Left-col A
left-col [] = [] ∷c []
left-col ((x ∷ row) ∷ A) with left-col A
... | col ∷c A′ = (x ∷ col) ∷c (row ∷ A′)

--------------------------------------------------------------------------
-- Column-wise view of a matrix, to allow for induction over the columns

data Column-wise {n} : ∀ {m} → Mat n m → Set c where
  []cw : Column-wise (replicate [])
  _∷cw_ : ∀ {m} {A : Mat n m}
    (xs : BaseVec S n)
    (cwA : Column-wise A)
    → Column-wise (zipWith _∷_ xs A)

private
  vec0-replicate : ∀ {a} {A : Set a} {n}
    → (xs : BaseVec (BaseVec A 0) n)
    → xs ≡ replicate []
  vec0-replicate [] = PE.refl
  vec0-replicate ([] ∷ xs) = PE.cong ([] ∷_) $ vec0-replicate xs

cw-view : ∀ {n m} (A : Mat n m) → Column-wise A
cw-view {m = ℕ.zero} A rewrite vec0-replicate A = []cw
cw-view {m = ℕ.suc m} A with left-col A
... | col ∷c A′ = col ∷cw (cw-view A′)
