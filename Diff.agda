module Diff where
import Level
open import Function
open import Data.Nat using (ℕ; suc; zero; _≤?_)
open import Data.List using (List; []; _∷_; length) renaming (map to listMap)
open import Data.Product using (_,_; ∃; ∃-syntax; uncurry) renaming (map to Σmap)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using () renaming (map′ to decMap)
import Algebra

module Diffs {L : Set}
             (_≟_ : ∀ (x y : L) → Dec (x ≡ y))
    where

  data Edit : Set where
    +_ -_ : L → Edit
    === : Edit

  Doc = List L
  Diff = List Edit

  {-- diff application --}
  data App : Diff → Doc → Doc → Set where
    mt     : App [] [] []
    add    : ∀ {x l l′ e} → App e l l′ → App (+ x ∷ e) l (x ∷ l′)
    sub    : ∀ {x l l′ e} → App e l l′ → App (- x ∷ e) (x ∷ l) l′
    keep   : ∀ {x l l′ e} → App e l l′ → App (=== ∷ e) (x ∷ l) (x ∷ l′)

  {-- diff wellformedness --}
  data _⊢_ : Doc → Diff → Set where
    mt    : [] ⊢ []
    add   : ∀ {x l e} → l ⊢ e →       l ⊢ (+ x ∷ e)
    sub   : ∀ {x l e} → l ⊢ e → (x ∷ l) ⊢ (- x ∷ e)
    keep  : ∀ {x l e} → l ⊢ e → (x ∷ l) ⊢ (=== ∷ e)

  {-- commonly implemented with DP, but not here --}
  open import Data.Bool using (if_then_else_)
  open import Relation.Nullary.Decidable using (⌊_⌋)
  shorter : ∀ {A : Set} → List A → List A → List A
  shorter xs ys =
    if ⌊ length xs ≤? length ys ⌋
    then xs
    else ys

  lcs : Doc → Doc → Diff
  lcs [] l′ = listMap +_ l′
  lcs l []  = listMap -_ l
  lcs (x ∷ l) (y ∷ l′) with x ≟ y
  ... | yes refl = (=== ∷ lcs l l′)
  ... | no x≠y   = shorter (- x ∷ lcs l (y ∷ l′))
                           (+ y ∷ lcs (x ∷ l) l′)

  shorter-ind : ∀ {A : Set} (P : List A → Set)
              → ∀ x y → P x → P y
              → P (shorter x y)
  shorter-ind P x y px py with length x ≤? length y
  ... | yes _ = px
  ... | no _  = py
