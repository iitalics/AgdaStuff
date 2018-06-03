open import Level using (Level; _⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open PE.≡-Reasoning

open import Data.Product using (proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; zipWith; map; foldr; foldl)

open import LinearAlgebra
open import LinearAlgebra.Transformations.Core

module LinearAlgebra.Transformations.Properties where

module One
  {c₁ c₂} (vectorSpace : VectorSpace c₁ c₂)
  where

  open VectorSpace vectorSpace
  open import LinearAlgebra.Transformations vectorSpaceOver vectorSpaceOver

  id-is-linear : IsLinearFn id
  id-is-linear = record
    { scale = λ _ _ → PE.refl
    ; sum = λ _ _ → PE.refl }

  scale-is-linear : ∀ k → IsLinearFn (k *_)
  scale-is-linear k = record
    { scale = λ j v → begin
        k * (j * v)    ≡⟨ PE.sym $ *-assoc k j v ⟩
        (k s* j) * v   ≡⟨ PE.cong (_* v) (s*-comm k j) ⟩
        (j s* k) * v   ≡⟨ *-assoc j k v ⟩
        j * (k * v) ∎
    ; sum = distribˡ k }

  negate-is-linear : IsLinearFn negate
  negate-is-linear = scale-is-linear s-1

  ∘-is-linear : ∀ {f g}
    → IsLinearFn f
    → IsLinearFn g
    → IsLinearFn (f ∘ g)
  ∘-is-linear {f} {g}
    record { scale = f-scale ; sum = f-sum }
    record { scale = g-scale ; sum = g-sum }
    = record
    { scale = λ k v → begin
        f (g (k * v))   ≡⟨ PE.cong f (g-scale k v) ⟩
        f (k * g v)     ≡⟨ f-scale k (g v) ⟩
        k * f (g v) ∎
    ; sum = λ v u → begin
        f (g (v + u))   ≡⟨ PE.cong f (g-sum v u) ⟩
        f (g v + g u)   ≡⟨ f-sum (g v) (g u) ⟩
        f (g v) + f (g u) ∎ }


module Two
  {s c₁ c₂} {scalar : Scalar s}
  (space₁ : VectorSpaceOver scalar c₁)
  (space₂ : VectorSpaceOver scalar c₂)
  where

  open Scalar scalar using ()
    renaming (Carrier to S)
  open VectorSpaceOver space₁ using ()
    renaming (V to V₁ ; v0 to v0₁ ; _+_ to _+₁_ ; _*_ to _*₁_ )
  open VectorSpaceOver space₂ using ()
    renaming (V to V₂ ; v0 to v0₂ ; _+_ to _+₂_ ; _*_ to _*₂_)

  import LinearAlgebra.Vec scalar as LAVec
  open LAVec.Combination space₁ using () renaming (combine to combine₁)
  open LAVec.Combination space₂ using () renaming (combine to combine₂)
  open import LinearAlgebra.Transformations space₁ space₂ using (IsLinearFn)

  -- T preserves the origin

  transform-zero : (T : V₁ → V₂)
    → LinearSum _+₁_ _+₂_ T
    → T v0₁ ≡ v0₂
  transform-zero T T-sum =
    from-+-zeroˡ (T v0₁) (T v0₁) (begin
      T v0₁ +₂ T _    ≡⟨ PE.sym (T-sum v0₁ _) ⟩
      T (v0₁ +₁ _)    ≡⟨ PE.cong T (proj₁ +-identity _) ⟩
      T _ ∎)
    where
      open VectorSpaceOver space₁ using (+-identity)
      open VectorSpaceOver space₂ using (from-+-zeroˡ)

  -- T can be lifted out of map / zipWith

  map-linear-scale : (T : V₁ → V₂)
    → LinearScale _*₁_ _*₂_ T
    → ∀ {n} (xs : Vec S n) (vs : Vec V₁ n)
    → map T (zipWith _*₁_ xs vs) ≡ zipWith _*₂_ xs (map T vs)
  map-linear-scale T T-scale [] [] = PE.refl
  map-linear-scale T T-scale (x ∷ xs) (v ∷ vs) rewrite
    T-scale x v | map-linear-scale _ T-scale xs vs
    = PE.refl

  -- T can be lifted out of foldr

  foldr-linear-sum : (T : V₁ → V₂)
    → LinearSum _+₁_ _+₂_ T
    → ∀ {n} (i : V₁) (vs : Vec V₁ n)
    → T (foldr _ _+₁_ i vs) ≡ foldr _ _+₂_ (T i) (map T vs)
  foldr-linear-sum T T-sum i [] = PE.refl
  foldr-linear-sum T T-sum i (v ∷ vs) rewrite
    T-sum v (foldr _ _+₁_ i vs) | foldr-linear-sum _ T-sum i vs
    = PE.refl

  -- T can be lifted out of foldl

  foldl-linear-sum : (T : V₁ → V₂)
    → LinearSum _+₁_ _+₂_ T
    → ∀ {n} (i : V₁) (vs : Vec V₁ n)
    → T (foldl _ _+₁_ i vs) ≡ foldl _ _+₂_ (T i) (map T vs)
  foldl-linear-sum T T-sum i [] = PE.refl
  foldl-linear-sum T T-sum i (v ∷ vs) rewrite
    foldl-linear-sum _ T-sum (i +₁ v) vs | T-sum i v
    = PE.refl

  -- T can be lifted out of linear combination

  combine-linear : (T : V₁ → V₂)
    → IsLinearFn T
    → ∀ {n} (xs : Vec S n) (vs : Vec V₁ n)
    → T (combine₁ xs vs) ≡ combine₂ xs (map T vs)
  combine-linear T (record { sum = sum ; scale = scale }) xs vs rewrite
    foldr-linear-sum T sum v0₁ (zipWith _*₁_ xs vs)
    | map-linear-scale T scale xs vs
    | transform-zero T sum
    = PE.refl

open One
open Two
