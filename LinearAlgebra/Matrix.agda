open import Function
open import Algebra.FunctionProperties.Core

open import Data.Nat using (ℕ)
open import Data.Vec
  using ( _∷_; []; map; replicate; zipWith; foldr; tabulate )
  renaming (Vec to BaseVec)

open import LinearAlgebra.Scalar

--------------------------------------------------------------------------
-- Matrices as 2-dimensional vector of scalars

module LinearAlgebra.Matrix
  {c} (scalar : Scalar c)
  where

open Scalar scalar
  using ()
  renaming ( Carrier to S
           ; 0# to s0 ; -1# to s-1
           ; _+_ to s+
           ; _*_ to s*
           ; -_ to s- )

open import LinearAlgebra.Vec scalar
  using ( Vec ; v0 ; essential ; _·_ )
  renaming ( _+_ to _v+_
           ; _*_ to _v*_ )

-- `Mat n m' is the type of matrices with `n' rows, `m' columns

Mat : ℕ → ℕ → Set c
Mat n m = BaseVec (BaseVec S m) n

-- Matrix operations:

-- zero matrix
m0 : ∀ {n m} → Mat n m
m0 = replicate v0

-- identity matrix
m1 : ∀ {n} → Mat n n
m1 = tabulate essential

-- matrix transpose
transpose : ∀ {n m} → Mat n m → Mat m n
transpose = foldr (Mat _) (zipWith _∷_) (replicate [])

-- matrix application
apply : ∀ {n m} → Mat n m → Vec m → Vec n
apply m v = map (v ·_) m
