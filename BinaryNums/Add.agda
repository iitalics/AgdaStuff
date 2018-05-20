open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import BinaryNums.Base

module BinaryNums.Add where

module _ where
  open import Data.Nat.Properties
  open SemiringSolver

  private
    lem-2*x+y = solve 2 (λ x y →
      x :* con 2 :+ y :* con 2
        :=
      (x :+ y) :* con 2) P.refl

    lem-s2*x+y = solve 2 (λ x y →
      x :* con 2 :+ (con 1 :+ y :* con 2)
        :=
      con 1 :+ (x :+ y) :* con 2) P.refl

  _+ᵇ_ : ∀ {n m} → Bin n → Bin m → Bin (n + m)
  _+ᵇ_ zero y = y
  _+ᵇ_ {n} x zero rewrite +-identityʳ n = x
  (_,0 {n} x) +ᵇ (_,0 {m} y) rewrite lem-2*x+y n m = (x +ᵇ y) ,0
  (_,0 {n} x) +ᵇ (_,1 {m} y) rewrite lem-s2*x+y n m = (x +ᵇ y) ,1
  (_,1 {n} x) +ᵇ (_,0 {m} y) rewrite lem-2*x+y n m = (x +ᵇ y) ,1
  (_,1 {n} x) +ᵇ (_,1 {m} y) rewrite lem-s2*x+y n m = sucᵇ (x +ᵇ y) ,0
