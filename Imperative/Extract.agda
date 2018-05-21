open import Function

open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Vec using (Vec; lookup; toList)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to natToString)

open import Imperative.Base

module Imperative.Extract where

data SExp : Set where
  sym  : String → SExp
  num  : ℕ → SExp
  list : List SExp → SExp

mutual
  sexpToString : SExp → String
  sexpToString (sym x) = x
  sexpToString (num c) = natToString c
  sexpToString (list l) = "(" <> sexpsToString l <> ")"

  sexpsToString : List SExp → String
  sexpsToString [] = ""
  sexpsToString (x ∷ []) = sexpToString x
  sexpsToString (x ∷ y ∷ l) = sexpToString x <> " " <> sexpsToString (y ∷ l)

Ids = Vec String

varToSexp : ∀ {n} → Ids n → Fin n → SExp
varToSexp Σ x = sym (lookup x Σ)

exToSexp : ∀ {n} → Ids n → Ex n → SExp
exToSexp Σ (cst c) = num c
exToSexp Σ (var x) = varToSexp Σ x
exToSexp Σ (e₁ +′ e₂) = list (sym "+" ∷ exToSexp Σ e₁ ∷ exToSexp Σ e₂ ∷ [])
exToSexp Σ (e₁ *′ e₂) = list (sym "*" ∷ exToSexp Σ e₁ ∷ exToSexp Σ e₂ ∷ [])
exToSexp Σ (1+ e) = list (sym "add1" ∷ exToSexp Σ e ∷ [])
exToSexp Σ (1- e) = list (sym "max" ∷ list (sym "sub1" ∷ exToSexp Σ e ∷ []) ∷ num 0 ∷ [])

¬prToSexp : ∀ {n} → Ids n → Pr n → SExp
¬prToSexp Σ (z? e) = list (sym "positive?" ∷ exToSexp Σ e ∷ [])
¬prToSexp Σ (nz? e) = list (sym "zero?" ∷ exToSexp Σ e ∷ [])
¬prToSexp Σ (e₁ =′ e₂) = list (sym "not" ∷ list (sym "=" ∷ exToSexp Σ e₁ ∷ exToSexp Σ e₂ ∷ []) ∷ [])
¬prToSexp Σ (e₁ ≤′ e₂) = list (sym ">" ∷ exToSexp Σ e₁ ∷ exToSexp Σ e₂ ∷ [])

stToSexps : ∀ {n} → Ids n → St n → List SExp
stToSexps Σ (x ≔ e) = list (sym "set!" ∷ varToSexp Σ x ∷ exToSexp Σ e ∷ []) ∷ []
stToSexps Σ (s₁ ⟫ s₂) = (stToSexps Σ s₁) ++ (stToSexps Σ s₂)
stToSexps Σ (while p s) = list (sym "do" ∷ list [] ∷ list (¬prToSexp Σ p ∷ []) ∷ stToSexps Σ s) ∷ []
stToSexps Σ no-op = []

stToSexp : ∀ {n} → String → Ids n → St n → SExp
stToSexp name Σ s =
  let args = map sym (toList Σ) in
  list (sym "define" ∷ list (sym name ∷ args)
         ∷ stToSexps Σ s
         ++ (list (sym "values" ∷ args) ∷ []))
