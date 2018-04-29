module BitCaseAnalysis where
import Level
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; pred) renaming (suc to s; zero to z)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable as ND using (True; toWitness)

data Bit : Set where
  `0 `1 : Bit

-- Decidable equality
_≟_ : ∀ (x y : Bit) → Dec (x ≡ y)
`0 ≟ `0 = yes refl
`0 ≟ `1 = no λ ()
`1 ≟ `0 = no λ ()
`1 ≟ `1 = yes refl

-- Case analysis proof "tactic"; proves general boolean
-- algebra expressions by checking every case.
module CA where
  open import Data.Vec using (Vec; []; _∷_)
  open import Data.List using (List; []; _∷_; map; _++_)
  open import Data.List.All using (all)
  open import Data.Vec.N-ary

  -- Generates every permutation of 'n' bits
  permutes : ∀ n → List (Vec Bit n)
  permutes z = [] ∷ []
  permutes (s n) = map (_∷_ `0) (permutes n)
                ++ map (_∷_ `1) (permutes n)

  private
    open import Data.List.All using (All; head)
    open import Data.List.All.Properties using (map-All; ++⁻ˡ; ++⁻ʳ)

    -- Permutations indeed cover all cases (expressed as n-ary)
    permutes→∀ⁿ : ∀ n {P : Vec Bit n → Set}
      → All P (permutes n)
      → ∀ⁿ n (curryⁿ P)
    permutes→∀ⁿ z = head
    permutes→∀ⁿ (s n) ps `0 = permutes→∀ⁿ n $ map-All $ ++⁻ˡ (map (_∷_ `0) (permutes n)) ps
    permutes→∀ⁿ (s n) ps `1 = permutes→∀ⁿ n $ map-All $ ++⁻ʳ (map (_∷_ `0) (permutes n)) ps

  -- Main case analysis solver
  -- usage, e.g.:
  --   not-not : ∀ x → not (not x) ≡ x
  --   not-not = case-analysis 1 (λ x → not (not x) , x)
  --
  -- In most cases agda can infer the equation so it can be omitted,
  -- which makes the follow expression valid and preferable:
  --   not-not : ∀ x → not (not x) ≡ x
  --   not-not = case-analysis 1 _
  case-analysis : ∀ n (E : N-ary n Bit (Bit × Bit))
    → let LHS = λ (xs : Vec Bit n) → proj₁ (E $ⁿ xs)
          RHS = λ (xs : Vec Bit n) → proj₂ (E $ⁿ xs) in
    {_ : True (all (λ xs → LHS xs ≟ RHS xs) (permutes n))}
    → ∀ⁿ n (curryⁿ (λ xs → LHS xs ≡ RHS xs))
  case-analysis n E {t} = permutes→∀ⁿ n (toWitness t)

infix 7 _OR_
infix 8 _AND_
infix 9 _XOR_

NOT : Bit → Bit
NOT `0 = `1
NOT `1 = `0

_XOR_ : Bit → Bit → Bit
`0 XOR b = b
`1 XOR b = NOT b

_AND_ : Bit → Bit → Bit
`0 AND x = `0
`1 AND x = x

_OR_ : Bit → Bit → Bit
`0 OR x = x
`1 OR x = `1

or-and-distr : ∀ a b c → a OR (b AND c) ≡ (a OR b) AND (a OR c)
or-and-distr = CA.case-analysis 3 _
and-or-distr : ∀ a b c → a AND (b OR c) ≡ (a AND b) OR (a AND c)
and-or-distr = CA.case-analysis 3 _

and-demorgan : ∀ a b → NOT (a AND b) ≡ (NOT a) OR (NOT b)
and-demorgan = CA.case-analysis 2 _
or-demorgan : ∀ a b → NOT (a OR b) ≡ (NOT a) AND (NOT b)
or-demorgan = CA.case-analysis 2 _

{-----------------------------------------------------------------}

open import Data.Vec using (Vec; _∷_; [])
open import Data.Fin using (Fin; raise; #_; toℕ; fromℕ≤) renaming (zero to fz; suc to fs)
open import Data.Nat as N using (_<_) renaming (⌊_/2⌋ to [_/2↓]; ⌈_/2⌉ to [_/2↑])
import Data.Nat.Properties as NP
import Data.Fin.Properties as FP

Bin : ℕ → Set
Bin = Vec Bit

2^ : ℕ → ℕ
2^ z = 1
2^ (s n) = 2^ n + 2^ n

module Helpers where

  toNat : ∀ {n} → Bin n → ℕ
  toNat [] = 0
  toNat (`0 ∷ bs) = toNat bs + toNat bs
  toNat (`1 ∷ bs) = s (toNat bs + toNat bs)

  toNat-< : ∀ n (bs : Bin n) → toNat bs < 2^ n
  toNat-< z [] = N.s≤s N.z≤n
  toNat-< (s n) (`0 ∷ bs)
    = NP.+-mono-< (toNat-< n bs) (toNat-< n bs)
  toNat-< (s n) (`1 ∷ bs) rewrite P.sym $ NP.+-suc (toNat bs) (toNat bs)
    = NP.+-mono-≤ (toNat-< n bs) (toNat-< n bs)

  mutual
    div2 : ∀ n → Fin (n + n) → Fin n
    div2 z ()
    div2 (s n) fz = # 0
    div2 (s z) (fs fz) = # 0
    div2 (s z) (fs (fs ()))
    div2 (s (s n)) (fs fz) = # 0
    div2 (s (s n)) (fs (fs x)) rewrite NP.+-suc n (s n) = fs (div2 (s n) x)

  lsb : ℕ → Bit
  lsb 0 = `0
  lsb 1 = `1
  lsb (s (s n)) = lsb n

module _ where
  open Helpers

  toFin : ∀ n → Bin n → Fin (2^ n)
  toFin n = fromℕ≤ ∘ toNat-< n

  fromFin : ∀ n → Fin (2^ n) → Bin n
  fromFin z     _ = []
  fromFin (s n) x = lsb (toℕ x) ∷ fromFin n (div2 _ x)

module Proof where
  open Helpers
  open N using (_≤_; s≤s; z≤n)

  lsb-+ : ∀ n → lsb (n + n) ≡ `0
  lsb-+ z = refl
  lsb-+ (s z) = refl
  lsb-+ (s (s n)) rewrite NP.+-suc n (s n) = lsb-+ (s n)

  div2-+ : ∀ n i (i<n : i < n)
    → div2 n (fromℕ≤ (NP.+-mono-< i<n i<n)) ≡ fromℕ≤ i<n
  div2-+ z i ()
  div2-+ (s z) i (s≤s cmp) with NP.+-mono-< (s≤s cmp) (s≤s cmp)
  div2-+ (s z) .0 (s≤s z≤n) | s≤s z≤n = refl

  div2-+ (s (s n)) i (s≤s cmp) with i | cmp | NP.+-mono-< (s≤s cmp) (s≤s cmp)
  ... | z | z≤n | s≤s z≤n = refl
  ... | s i′ | s≤s cmp- | s≤s mono = {!!}

  from-to : ∀ n bs → fromFin n (toFin n bs) ≡ bs
  from-to z [] = refl
  from-to (s n) (`0 ∷ bs)
    rewrite FP.toℕ-fromℕ≤ (toNat-< (s n) (`0 ∷ bs))
    | lsb-+ (toNat bs)
    | from-to n bs
    | P.sym $ FP.fromℕ-def (toNat bs + toNat bs)
    = {!!}

  from-to (s n) (`1 ∷ bs) = {!!}
