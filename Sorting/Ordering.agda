open import Relation.Unary as U using (Pred)
open import Relation.Binary as B using (Rel; REL)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.All using (All; []; _∷_)

module Sorting.Ordering
  {a r}
  {A : Set a}
  {_≤_ : Rel A r}
  (isTO : B.IsTotalOrder _≡_ _≤_)
  where

open B.IsTotalOrder isTO
  using ()
  renaming (trans to ≤-trans)

-- Ordered list predicate
data Ord : Pred (List A) r where
  [] : Ord []
  sing : ∀ {x} → Ord (x ∷ [])
  _∷_ : ∀ {x y xs} → (x ≤ y) → Ord (y ∷ xs) → Ord (x ∷ y ∷ xs)

-- Lower/upper bounds
Min Max : REL A (List A) _
Min x = All λ e → x ≤ e
Max x = All λ e → e ≤ x

module Properties where
  -- You can cons a minimal element to get an ordered list
  min-∷ : ∀ {b xs} → Min b xs → Ord xs → Ord (b ∷ xs)
  min-∷ [] [] = sing
  min-∷ (b≤x ∷ _) sing = b≤x ∷ sing
  min-∷ (b≤x ∷ _) (x≤y ∷ o) = b≤x ∷ x≤y ∷ o

  -- Stuffing a pivot between two ordered lists forms an ordered list
  stuff : ∀ {piv xs ys}
    → Max piv xs → Ord xs
    → Min piv ys → Ord ys
    → Ord (xs ++ piv ∷ ys)
  stuff [] []                  my oys = min-∷ my oys
  stuff (x≤p ∷ _)  sing        my oys = x≤p ∷ min-∷ my oys
  stuff (_   ∷ mx) (x≤y ∷ oxs) my oys = x≤y ∷ stuff mx oxs my oys
