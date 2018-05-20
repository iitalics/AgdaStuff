open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Nat using (ℕ; _*_)

open import BinaryNums.Base
open import BinaryNums.Add

module BinaryNums.Mul where

module _ where
  open import Data.Nat.Properties

  private
    lem : ∀ x y → (x * 2 * y ≡ x * y * 2)
    lem x y
      rewrite *-assoc x 2 y
        | *-comm 2 y
      = P.sym $ *-assoc x y 2

  _*ᵇ_ : ∀ {n m} → Bin n → Bin m → Bin (n * m)
  _*ᵇ_ zero y = zero
  _*ᵇ_ {m = m} (_,0 {n} x) y
    rewrite lem n m
    = (x *ᵇ y) ,0
  _*ᵇ_ {m = m} (_,1 {n} x) y
    rewrite lem n m
    = y +ᵇ ((x *ᵇ y) ,0)
