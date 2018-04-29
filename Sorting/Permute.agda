open import Function
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Unary as U using (Pred)
open import Relation.Binary as B
  using (Rel; REL; _⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
import Relation.Binary.PropositionalEquality as PE
import Algebra as Alg
import Algebra.FunctionProperties as FunP

open import Data.Product using (proj₁; proj₂)
open import Data.List using (List; []; _++_; _∷_; _∷ʳ_)
open import Data.Star using (Star; ε; _◅_; _◅◅_)
--import Data.List.Properties as ListP

import Data.Star.Properties as StarP

module Sorting.Permute
  {a} {A : Set a}
  where

infix 4 _∼ₚ_ _≈ₚ_

-- "x ∼ₚ y" means x and y are the same except with one element swapped
data _∼ₚ_ : Rel (List A) a where
  skip : ∀ {x xs ys} → (xs ∼ₚ ys) → (x ∷ xs ∼ₚ x ∷ ys)
  swap : ∀ {x y xs} → (x ∷ y ∷ xs ∼ₚ y ∷ x ∷ xs)

-- "x ≈ₚ y" means x and y are permutations, e.g. repeated swaps
_≈ₚ_ = Star _∼ₚ_

module Properties where
  private
    module LM = Alg.Monoid (Data.List.monoid A)
    ++-idʳ = proj₂ LM.identity
    ++-assoc = LM.assoc

  -- Free _≈ₚ_ preorder courtesy of Data.Star
  preorder : B.Preorder _ _ _
  preorder = StarP.preorder _∼ₚ_
  open B.Preorder preorder public
    using (isPreorder; refl; trans)

  -- Cons element onto a permutation (e.g. '132'~'321' -> '4123'~'4321')
  ∷-perm : ∀ {x} → (_∷_ x) Preserves _≈ₚ_ ⟶ _≈ₚ_
  ∷-perm ε = ε
  ∷-perm (x~y ◅ y~z) = skip x~y ◅ ∷-perm y~z

  -- Move an element to the front by repeated swaps
  head-perm : ∀ i xs ys → (xs ++ i ∷ ys) ≈ₚ (i ∷ xs ++ ys)
  head-perm i []       ys = refl
  head-perm i (x ∷ xs) ys = ∷-perm (head-perm i xs ys) ◅◅ swap ◅ ε

  -- Append (snoc) element onto a swap
  ∷ʳ-swap : ∀ z → (flip _∷ʳ_ z) Preserves _∼ₚ_ ⟶ _∼ₚ_
  ∷ʳ-swap z (skip x~y) = skip (∷ʳ-swap z x~y)
  ∷ʳ-swap z swap       = swap

  -- Append list onto a swap
  ++ʳ-swap : ∀ xs → (flip _++_ xs) Preserves _∼ₚ_ ⟶ _∼ₚ_
  ++ʳ-swap [] {xs} {ys} x~y rewrite ++-idʳ xs | ++-idʳ ys = x~y
  ++ʳ-swap (x ∷ xs) {ys} {zs} y~z rewrite
      PE.sym $ ++-assoc ys (x ∷ []) xs
    | PE.sym $ ++-assoc zs (x ∷ []) xs
    = ++ʳ-swap xs (∷ʳ-swap x y~z)

  -- Prepend list onto a permutation
  ++ˡ-perm : ∀ xs → (_++_ xs) Preserves _≈ₚ_ ⟶ _≈ₚ_
  ++ˡ-perm []       y~z = y~z
  ++ˡ-perm (_ ∷ xs) y~z = ∷-perm (++ˡ-perm xs y~z)

  -- Append two permutations (e.g. '123/321'+'45/54' => '13245'/'32154')
  ++-perm : _++_ Preserves₂ _≈ₚ_ ⟶ _≈ₚ_ ⟶ _≈ₚ_
  ++-perm {xs} ε      u~v = ++ˡ-perm xs u~v
  ++-perm (x~y ◅ y~z) u~v = ++ʳ-swap _ x~y ◅ ++-perm y~z u~v
