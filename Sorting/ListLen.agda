open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core as B using (Rel)
import Induction as I

open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; length; filter)

import Induction.Nat as NatInd
import Induction.WellFounded as WF
import Data.Nat.Properties as NatP

module Sorting.ListLen
  {a} {A : Set a}
  where

-- Length relations based on < and ≤
infix 4 _<ₗₑₙ_ _≤ₗₑₙ_
_<ₗₑₙ_ _≤ₗₑₙ_ : Rel (List A) _
_<ₗₑₙ_ = _<_ on length
_≤ₗₑₙ_ = _≤_ on length

-- Well founded induction on <ₗₑₙ
len-wf : WF.Well-founded _<ₗₑₙ_
len-wf = WF.Inverse-image.well-founded length NatInd.<-well-founded
len-Rec : ∀ ℓ → I.RecStruct (List A) ℓ _
len-Rec _ = WF.WfRec _<ₗₑₙ_
len-rec : ∀ {ℓ} → I.Recursor (len-Rec ℓ)
len-rec = WF.All.wfRec len-wf _

module Properties where
  len-tail : ∀ x xs → (xs <ₗₑₙ x ∷ xs)
  len-tail _ _ = NatP.≤-refl

  len-filter : ∀ {p} {P : Pred A p} (P? : U.Decidable P) (xs : List A)
    → filter P? xs ≤ₗₑₙ xs
  len-filter P? [] = z≤n
  len-filter P? (x ∷ xs) with P? x
  ... | yes _ = s≤s (len-filter P? xs)
  ... | no  _ = NatP.≤-step (len-filter P? xs)
