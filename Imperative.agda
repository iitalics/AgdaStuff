open import Level using (_⊔_) renaming (suc to lsuc)
open import Function

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; #_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.List using (List; _∷_; [])

module Imperative where

open import Imperative.Base public
open import Imperative.Extract

X = # 0
Y = # 1

fact : St 2
fact =
  Y ≔ (cst 1) ⟫         -- ρ = [n, 1]
  while (nz? (var X))   -- invar: ρ = [k, n!/k!]
  (
    Y ≔ var Y *′ var X ⟫
    X ≔ 1- (var X)
  )                     -- postcond: ρ = [0, n!]

fact-sexp = stToSexp "fact" ("x" ∷ "y" ∷ []) fact
fact-extr = sexpToString fact-sexp
