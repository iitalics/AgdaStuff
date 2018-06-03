open import Level using (_⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≗_)

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec
  using ( _∷_; []; foldr; map; replicate; zipWith; tabulate)
  renaming (Vec to BaseVec)

module LinearAlgebra.Matrix.Lemmas where

map-on₂ : ∀ {n} {a b c d}
  {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : A → C) (_*_ : B → C → D) (l : BaseVec A n)
  → map (λ x → f x * g x) l ≡ zipWith _*_ (map f l) (map g l)
map-on₂ f g _*_ [] = PE.refl
map-on₂ f g _*_ (x ∷ l) = PE.cong (_ ∷_) $ map-on₂ f g _*_ l

tabulate-cong : ∀ {n} {a} {A : Set a}
  (f g : Fin n → A)
  → f ≗ g
  → tabulate f ≡ tabulate g
tabulate-cong {0}     f g f~g = PE.refl
tabulate-cong {suc n} f g f~g = PE.cong₂ _∷_ (f~g zero) (tabulate-cong _ _ (f~g ∘ suc))

map-const : ∀ {n} {a b} {A : Set a} {B : Set b} (x : A)
  → map (const x) ≗ const {B = BaseVec B n} (replicate {n = n} x)
map-const x []      = PE.refl
map-const x (_ ∷ l) = PE.cong₂ _∷_ PE.refl (map-const x l)

zipWith-const₁ : ∀ {n} {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (_*_ : A → B → C) (k : A) (l : BaseVec B n)
  → map (k *_) l ≡ zipWith _*_ (replicate k) l
zipWith-const₁ _*_ k [] = PE.refl
zipWith-const₁ _*_ k (x ∷ l) = PE.cong ((k * x) ∷_) (zipWith-const₁ _*_ k l)

foldr-replicate : ∀ {a b} {A : Set a} {B : Set b}
  → (_+_ : A → B → B) (i : B) (x : A)
  → (x + i ≡ i)
  → ∀ n → foldr _ _+_ i (replicate {n = n} x) ≡ i
foldr-replicate _+_ i x prop 0 = PE.refl
foldr-replicate _+_ i x prop (suc n) rewrite
  foldr-replicate _+_ i x prop n
  = prop
