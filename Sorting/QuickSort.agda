open import Function
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction) renaming (¬? to not)
open import Relation.Unary as U using (Pred)
open import Relation.Binary as B using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Sum using (inj₁; inj₂)
open import Data.List     using (List; []; _∷_; _++_; filter)
open import Data.List.All using (All;  []; _∷_) renaming (map to allMap)

import Sorting.Ordering
import Sorting.ListLen as Len

import Data.Nat.Properties as NatP
import Data.List.All.Properties as AllP

module Sorting.QuickSort
  {a r}
  {A : Set a}
  {_≤_ : Rel A r}
  (isDTO : B.IsDecTotalOrder _≡_ _≤_)
  where

  open B.IsDecTotalOrder isDTO
    using (_≤?_; isTotalOrder)
    renaming (total to ≤-total)

  {------------------------------------------------------------}

  -- Partitioning functions
  below above : A → List A → List A
  below piv = filter λ x → x ≤? piv
  above piv = filter λ x → not (x ≤? piv)

  -- 'QSort l' represents a way to sort 'l' with quicksort
  -- This inductive type helps immensely with proofs
  data QSort : List A → Set a where
    mt : QSort []
    ne : ∀ p {l} → QSort (below p l) → QSort (above p l) → QSort (p ∷ l)

  -- Compute a 'QSort' for the given list, using well-founded induction
  -- on the list length
  qsort′ : ∀ l → QSort l
  qsort′ = Len.len-rec _ λ
    { [] _ → mt
    ; (piv ∷ l) sort →
      let xs = below piv l
          ys = above piv l
          qs-xs = sort xs (NatP.<-transʳ (len-filter _ l) (len-tail piv l))
          qs-ys = sort ys (NatP.<-transʳ (len-filter _ l) (len-tail piv l))
      in ne piv qs-xs qs-ys }
    where
      open Len.Properties

  -- Obtain the sorted list
  toList : ∀ {l} → QSort l → List A
  toList mt = []
  toList (ne piv xs ys) = toList xs ++ piv ∷ toList ys

  -- "Real" quicksort algorithm
  qsort : List A → List A
  qsort = toList ∘ qsort′

  {------------------------------------------------------------}

  module Properties where
    open Sorting.Ordering isTotalOrder
      renaming (module Properties to OrdP)

    -- A predicate remains true after applying qsort
    qsort-retain : ∀ {l : List A} (qs : QSort l)
      {p} {P : Pred A p} → All P l → All P (toList qs)
    qsort-retain mt [] = []
    qsort-retain (ne piv xs ys) (p-piv ∷ p-rest) =
      let p-xs = AllP.filter⁺₂ _ p-rest
          p-ys = AllP.filter⁺₂ _ p-rest
      in AllP.++⁺ (qsort-retain xs p-xs)
           (p-piv ∷ qsort-retain ys p-ys)

    -- The pivot is the minimum/maximum of either half
    below-max : ∀ piv l → Max piv (below piv l)
    above-min : ∀ piv l → Min piv (above piv l)
    below-max _ = AllP.filter⁺₁ _
    above-min _ = allMap ≰⇒≥ ∘ AllP.filter⁺₁ _
      where
        ≰⇒≥ : ∀ {x y} → ¬ (x ≤ y) → (y ≤ x)
        ≰⇒≥ {x} {y} x>y with ≤-total y x
        ... | inj₁ y≤x = y≤x
        ... | inj₂ x≤y = contradiction x≤y x>y

    -- QSort toList is ordered
    qsort-ord′ : ∀ {l} (qs : QSort l) → Ord (toList qs)
    qsort-ord′ mt = []
    qsort-ord′ {_ ∷ l} (ne piv xs ys) =
      let piv≥xs = qsort-retain xs (below-max piv l)
          piv≤ys = qsort-retain ys (above-min piv l)
      in OrdP.stuff
           piv≥xs (qsort-ord′ xs)
           piv≤ys (qsort-ord′ ys)

    -- qsort is ordered !!!!!!!
    qsort-ord : ∀ l → Ord (qsort l)
    qsort-ord = qsort-ord′ ∘ qsort′
