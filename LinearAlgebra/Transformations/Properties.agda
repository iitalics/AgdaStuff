open import Level using (Level; _⊔_)
open import Function
open import Algebra.FunctionProperties.Core
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open PE.≡-Reasoning

open import Data.Vec
  using (Vec; []; _∷_; zipWith; map; foldr; foldl)

open import LinearAlgebra
open import LinearAlgebra.Transformations.Core

module LinearAlgebra.Transformations.Properties
  where

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

  open One

  module Two
    {s c₁ c₂} {scalar : Scalar s}
    (space₁ : VectorSpaceOver scalar c₁)
    (space₂ : VectorSpaceOver scalar c₂)
    where

    open Scalar scalar
      renaming (Carrier to S)

    open VectorSpaceOver space₁
      using ()
      renaming (V to V₁ ; _+_ to _+₁_ ; _*_ to _*₁_ )

    open VectorSpaceOver space₂
      using ()
      renaming (V to V₂ ; _+_ to _+₂_ ; _*_ to _*₂_)


    -- LinearScale can be lifted out of map / zipWith

    map-linear-scale : (T : V₁ → V₂)
      → LinearScale _*₁_ _*₂_ T
      → ∀ {n} (xs : Vec S n) (vs : Vec V₁ n)
      → map T (zipWith _*₁_ xs vs) ≡ zipWith _*₂_ xs (map T vs)
    map-linear-scale T T-scale [] [] = PE.refl
    map-linear-scale T T-scale (x ∷ xs) (v ∷ vs) =
      PE.cong₂ _∷_ (T-scale x v) (map-linear-scale _ T-scale xs vs)

    -- LinearSum can be lifted out of foldr

    foldr-linear-sum : (T : V₁ → V₂)
      → LinearSum _+₁_ _+₂_ T
      → ∀ {n} (i : V₁) (vs : Vec V₁ n)
      → T (foldr _ _+₁_ i vs) ≡ foldr _ _+₂_ (T i) (map T vs)
    foldr-linear-sum T T-sum i [] = PE.refl
    foldr-linear-sum T T-sum i (v ∷ vs) = begin
      T (v +₁ foldr _ _+₁_ i vs)     ≡⟨ T-sum v _ ⟩
      T v +₂ T (foldr _ _+₁_ i vs)   ≡⟨ PE.cong (T v +₂_) $ foldr-linear-sum _ T-sum i vs ⟩
      T v +₂ (foldr _ _+₂_ (T i) (map T vs)) ∎

    -- LinearSum can be lifted out of foldl

    foldl-linear-sum : (T : V₁ → V₂)
      → LinearSum _+₁_ _+₂_ T
      → ∀ {n} (i : V₁) (vs : Vec V₁ n)
      → T (foldl _ _+₁_ i vs) ≡ foldl _ _+₂_ (T i) (map T vs)
    foldl-linear-sum T T-sum i [] = PE.refl
    foldl-linear-sum T T-sum i (v ∷ vs) = begin
      T (foldl _ _+₁_ (i +₁ v) vs)          ≡⟨ foldl-linear-sum _ T-sum (i +₁ v) vs ⟩
      foldl _ _+₂_ (T (i +₁ v)) (map T vs)  ≡⟨ PE.cong (λ x → foldl _ _ x (map T vs)) $ T-sum i v ⟩
      foldl _ _+₂_ (T i +₂ T v) (map T vs)  ∎
