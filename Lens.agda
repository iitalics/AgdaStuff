open import Level as Lv using (_⊔_) renaming (zero to ℓ0)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≗_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary as B using (Rel)
open import Relation.Unary  as U using (Pred; _∈_; _∉_)
open import Data.Integer using (ℤ)
open import Data.List using (List)
open import Data.String using (String)
open PE.≡-Reasoning

module Lens where

record IsFunctionalUpdate
  {c a t}

  (τ : Pred (Set a) t)
  (C : ∀ {A} → (A ∈ τ) → Set c)

  (get : ∀ {A} {{pA : A ∈ τ}} → C pA → A)
  (put : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → B → C pB)

  : Set (c ⊔ t ⊔ Lv.suc a) where
  field
    put-get : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} (ca : C pA) (b : B)
      → get (put ca b) ≡ b

    get-put : ∀ {A} {{pA : A ∈ τ}} (ca : C pA)
      → put ca (get ca) ≡ ca

    put-put : ∀ {X Y Z} {{pX : X ∈ τ}} {{pY : Y ∈ τ}} {{pZ : Z ∈ τ}} (cx : C pX) (y : Y) (z : Z)
      → put (put cx y) z ≡ put cx z

  modify : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → (A → B) → C pB
  modify ca f = put ca (f (get ca))

  modify-modify : ∀ {X Y Z} {{pX : X ∈ τ}} {{pY : Y ∈ τ}} {{pZ : Z ∈ τ}}
    → (cx : C pX) (f : X → Y) (g : Y → Z)
    → modify (modify cx f) g ≡ modify cx (g ∘ f)
  modify-modify cx f g =
    let put/f = put cx (f (get cx)) in
    begin
      modify (modify cx f) g       ≡⟨ PE.cong (put put/f ∘ g) (put-get cx (f _)) ⟩
      put put/f (g (f (get cx)))   ≡⟨ put-put cx (f _) (g _) ⟩
      modify cx (g ∘ f)             ∎

record SetOfSets (A : Set) : Set where
  constructor yep


module IdentityLens where

  τ = SetOfSets

  C : ∀ {A} → (A ∈ τ) → Set
  C {A} _ = A

  get : ∀ {A} {{pA : A ∈ τ}} → C pA → A
  get ca = ca

  put : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → B → C pB
  put ca b = b

  isFnUpdate : IsFunctionalUpdate τ C get put
  isFnUpdate = record
    { put-get = λ {A} ⦃ pA ⦄ ca a → PE.refl
    ; get-put = λ {A} ⦃ pA ⦄ ca → PE.refl
    ; put-put = λ {X} {Y} {Z} ⦃ pX ⦄ ⦃ pY ⦄ ⦃ pZ ⦄ cx y z → PE.refl }


module FstLens {X : Set} where

  τ = SetOfSets

  C : ∀ {A} → (A ∈ τ) → Set
  C {A} pA = A × X

  get : ∀ {A} {{pA : A ∈ τ}} → C pA → A
  get (a , x) = a

  put : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → B → C pB
  put (a , x) b = (b , x)

  isFnUpdate : IsFunctionalUpdate τ C get put
  isFnUpdate = record
    { put-get = λ { (_ , _) _ → PE.refl }
    ; get-put = λ { (_ , _) → PE.refl }
    ; put-put = λ { (_ , _) _ _ → PE.refl } }


module SndLens {X : Set} where

  τ = SetOfSets

  C : ∀ {A} → (A ∈ τ) → Set
  C {A} pA = X × A

  get : ∀ {A} {{pA : A ∈ τ}} → C pA → A
  get (x , a) = a

  put : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → B → C pB
  put (x , a) b = (x , b)

  isFnUpdate : IsFunctionalUpdate τ C get put
  isFnUpdate = record
    { put-get = λ { (_ , _) _ → PE.refl }
    ; get-put = λ { (_ , _) → PE.refl }
    ; put-put = λ { (_ , _) _ _ → PE.refl } }


module AddLens where
  open import Data.Integer
  open import Data.Integer.Properties

  data τ : Set → Set where
    is-int : ℤ ∈ τ

  C : ∀ {A} → (A ∈ τ) → Set
  C is-int = ℤ

  get : ∀ {A} {{pA : A ∈ τ}} → C pA → A
  get ⦃ is-int ⦄ ca = suc ca

  put : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → B → C pB
  put ⦃ is-int ⦄ ⦃ is-int ⦄ ca b = pred b

  put-get : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} (ca : C pA) (b : B)
    → get (put ca b) ≡ b
  put-get ⦃ is-int ⦄ ⦃ is-int ⦄ ca a = begin
    + 1 + (- + 1 + a)     ≡⟨ PE.sym (+-assoc (+ 1) (- + 1) a) ⟩
    (+ 0) + a             ≡⟨ +-identityˡ a ⟩
    a                      ∎

  get-put : ∀ {A} {{pA : A ∈ τ}} (ca : C pA)
    → put ca (get ca) ≡ ca
  get-put {.ℤ} ⦃ is-int ⦄ ca = begin
    - + 1 + (+ 1 + ca)   ≡⟨ PE.sym (+-assoc (- + 1) (+ 1) ca) ⟩
    (+ 0) + ca           ≡⟨ +-identityˡ ca ⟩
    ca                    ∎

  put-put : ∀ {X Y Z} {{pX : X ∈ τ}} {{pY : Y ∈ τ}} {{pZ : Z ∈ τ}} (cx : C pX) (y : Y) (z : Z)
    → put (put cx y) z ≡ put cx z
  put-put ⦃ is-int ⦄ ⦃ is-int ⦄ ⦃ is-int ⦄ cx y z = PE.refl

  isFnUpdate : IsFunctionalUpdate τ C get put
  isFnUpdate = record
    { put-get = put-get
    ; get-put = get-put
    ; put-put = put-put }


module Examples where

  five = IdentityLens.get 5

  foo = FstLens.get (SndLens.put (2 , 3) "a")
