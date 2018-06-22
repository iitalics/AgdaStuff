open import Level as Lv using (_⊔_) renaming (zero to ℓ0)
open import Function
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≗_)
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Binary as B using (Rel)
open import Relation.Unary  as U using (Pred; _∈_; _∉_)
open import Data.Integer hiding (_⊔_)
open import Data.List using (List)
open import Data.String using (String)
open PE.≡-Reasoning

module Lens where

record SetOfSets (A : Set) : Set where
  constructor yep

data Only (A : Set) : Pred Set ℓ0 where
  only : Only A A

instance
  reflOnly : ∀ {A : Set} → Only A A
  reflOnly = only

----------------------------------------------------------------------

Container : ∀ {a t} (τ : Pred (Set a) t) (ℓ : Lv.Level) → Set (Lv.suc (ℓ ⊔ a) ⊔ t)
Container τ ℓ = ∀ {A} → (A ∈ τ) → Set ℓ

Get Put Modify : ∀ {c a t} (τ : Pred (Set a) t) (C : Container τ c) → Set _
Get τ C = ∀ {A} {{pA : A ∈ τ}} → C pA → A
Put τ C = ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → B → C pB
Modify τ C = ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} → C pA → (A → B) → C pB

record IsFunctionalUpdate
  {c a t}
  (τ : Pred (Set a) t)
  (C : Container τ c)
  (get : Get τ C)
  (put : Put τ C)
  : Set (c ⊔ t ⊔ Lv.suc a) where
  field
    put-get : ∀ {A B} {{pA : A ∈ τ}} {{pB : B ∈ τ}} (ca : C pA) (b : B)
      → get (put ca b) ≡ b

    get-put : ∀ {A} {{pA : A ∈ τ}} (ca : C pA)
      → put ca (get ca) ≡ ca

    put-put : ∀ {X Y Z} {{pX : X ∈ τ}} {{pY : Y ∈ τ}} {{pZ : Z ∈ τ}} (cx : C pX) (y : Y) (z : Z)
      → put (put cx y) z ≡ put cx z

  modify : Modify τ C
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

-------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------

LENS : ∀ (a t ℓ : Lv.Level) → Set _
LENS a t ℓ = ∀ (τ : Pred (Set a) t) (C : Container τ a) → Set ℓ

record IsLens
  {a t ℓ}
  (L : LENS a t ℓ)
  : Set (Lv.suc (Lv.suc a ⊔ t ⊔ ℓ))
  where
  field
    makeLens : ∀ {τ : Pred (Set a) t} {C : Container τ a}
      → (get : Get τ C)
      → (put : Put τ C)
      → IsFunctionalUpdate τ C get put
      → L τ C

    get : ∀ {τ : Pred (Set a) t} {C : Container τ a}
      → L τ C
      → Get τ C

    put : ∀ {τ : Pred (Set a) t} {C : Container τ a}
      → L τ C
      → Put τ C

    isFnUpdate : ∀ {τ : Pred (Set a) t} {C : Container τ a} (l : L τ C)
      → IsFunctionalUpdate τ C (get l) (put l)

  thrush : ∀
    {τ σ : Pred (Set a) t}
    {C : Container τ a}
    {D : Container σ a}
    (pD : ∀ {A} (pA : A ∈ σ) → D pA ∈ τ)
    → L τ C
    → L σ D
    → L σ (C ∘ pD)
  thrush pD l1 l2 = makeLens
    (λ cda →
      let
        da = get l1 {{pD _}} cda
        a = get l2 da
      in a)
    (λ cda b →
      let
        da = get l1 cda
        db = put l2 da b
        cdb = put l1 {{pD _}} {{pD _}} cda db
      in cdb)
    (record
      { put-get = λ {{pA}} {{pB}} cda b →
        let
          instance pDA = pD pA ; pDB = pD pB
          get1a = get l1 {{pD pA}}
          get1b = get l1 {{pD pB}}
          get2a = get l2 {{pA}}
          get2b = get l2 {{pB}}
          put1 = put l1 {{pD pA}} {{pD pB}}
          put2 = put l2 {{pA}} {{pB}}
        in
        begin
          get2b (get1b (put1 cda (put2 (get1a cda) b)))
            ≡⟨ PE.cong get2b (FU1.put-get cda _) ⟩
          get2b (put2 (get1a cda) b)
            ≡⟨ FU2.put-get (get1a cda) b ⟩
          b
            ∎

      ; get-put = λ {{pA}} ca →
        let
          instance pDA = pD pA
          put1 = put l1 {{pD pA}} {{pD pA}}
          put2 = put l2 {{pA}} {{pA}}
          get1 = get l1
          get2 = get l2
        in
        begin
          put1 ca (put2 (get1 ca) (get2 (get1 ca)))
            ≡⟨ PE.cong (put1 ca) (FU2.get-put (get1 ca)) ⟩
          put1 ca (get1 ca)
            ≡⟨ FU1.get-put ca ⟩
          ca
            ∎

      ; put-put = λ {{pX}} {{pY}} {{pZ}} cdx y z →
        let
          instance pDX = pD pX ; pDY = pD pY ; pDZ = pD pZ
          put1xy = put l1 {{pD pX}} {{pD pY}}
          put1yz = put l1 {{pD pY}} {{pD pZ}}
          put1xz = put l1 {{pD pX}} {{pD pZ}}
          put2xy = put l2 {{pX}} {{pY}}
          put2yz = put l2 {{pY}} {{pZ}}
          put2xz = put l2 {{pX}} {{pZ}}
          get1x = get l1 {{pD pX}}
          get1y = get l1 {{pD pY}}
        in
        begin
          put1yz (put1xy cdx (put2xy (get1x cdx) y))
          (put2yz (get1y (put1xy cdx (put2xy (get1x cdx) y))) z)
            ≡⟨ PE.cong (λ a → put1yz (put1xy cdx (put2xy (get1x cdx) y)) (put2yz a z))
                (FU1.put-get cdx _) ⟩
          put1yz (put1xy cdx (put2xy (get1x cdx) y))
          (put2yz (put2xy (get1x cdx) y) z)
            ≡⟨ PE.cong (put1yz (put1xy cdx (put2xy (get1x cdx) y)))
                (FU2.put-put (get1x cdx) y z) ⟩
          put1yz (put1xy cdx (put2xy (get1x cdx) y)) (put2xz (get1x cdx) z)
            ≡⟨ FU1.put-put cdx _ _ ⟩
          put1xz cdx (put2xz (get1x cdx) z)
            ∎
      })
    where
      module FU1 = IsFunctionalUpdate (isFnUpdate l1)
      module FU2 = IsFunctionalUpdate (isFnUpdate l2)

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

module Lens1 where

  record L (τ : Pred Set ℓ0) (C : Container τ ℓ0) : Set (Lv.suc ℓ0) where
    constructor mkL
    field
      get : Get τ C
      put : Put τ C
      isFnUpdate : IsFunctionalUpdate τ C get put

  makeLens : ∀ {τ : Pred Set ℓ0} {C : Container τ ℓ0}
    → (get : Get τ C)
    → (put : Put τ C)
    → IsFunctionalUpdate τ C get put
    → L τ C
  makeLens = mkL

  isLens : IsLens L
  isLens = record
    { makeLens = makeLens
    ; get = L.get
    ; put = L.put
    ; isFnUpdate = L.isFnUpdate }

------------------------------------------------------------------------

module MakeExamples
  {L : LENS ℓ0 ℓ0 (Lv.suc ℓ0)}
  (isLens : IsLens L)
  where

  open IsLens isLens public

  idLens : L SetOfSets λ {A} pA → A
  idLens = makeLens
    id
    (const id)
    (record
      { put-get = λ _ _   → PE.refl
      ; get-put = λ _     → PE.refl
      ; put-put = λ _ _ _ → PE.refl })

  fstLens : ∀ {X : Set} → L SetOfSets λ {A} pA → A × X
  fstLens = makeLens
    fst
    (λ { (_ , x) b → (b , x) })
    (record
      { put-get = λ { (_ , _) _   → PE.refl }
      ; get-put = λ { (_ , _)     → PE.refl }
      ; put-put = λ { (_ , _) _ _ → PE.refl } })

  sndLens : ∀ {X : Set} → L SetOfSets λ {A} pA → X × A
  sndLens = makeLens
    snd
    (λ { (x , _) b → (x , b) })
    (record
      { put-get = λ { (_ , _) _   → PE.refl }
      ; get-put = λ { (_ , _)     → PE.refl }
      ; put-put = λ { (_ , _) _ _ → PE.refl } })

  plusLens : ℤ → L (Only ℤ) (const ℤ)
  plusLens off = makeLens
    (λ { {{pA = only}} x   → (x + off) })
    (λ { {{pB = only}} _ y → (y - off) })
    (record
      { put-get = λ { {{only}} {{only}} ca b → plusLemma b (- off) off (+-inverseˡ off) }
      ; get-put = λ { {{only}} ca → plusLemma ca off (- off) (+-inverseʳ off) }
      ; put-put = λ { {{only}} {{only}} {{only}} cx y z → PE.refl }})
    where
      open import Data.Integer.Properties
      plusLemma : ∀ b x y → (x + y ≡ + 0) → (b + x + y) ≡ b
      plusLemma b x y x+y=0 rewrite
        +-assoc b x y | x+y=0
        = +-identityʳ b

  add5fst : ∀ {X : Set} → L (Only ℤ) λ {A} pA → ℤ × X
  add5fst = thrush (λ _ → yep)
    fstLens
    (plusLens (+ 5))


module Examples1 where
  open MakeExamples Lens1.isLens

  add5fstS = add5fst {String}

  test1 : get add5fst (+ 3 , "hi") ≡ + 8
  test1 = PE.refl

  -- C A = Only ℤ

  test2 : put add5fst {A = ℤ} (+ 3 , "hi") (+ 42) ≡ (+ 37 , "hi")
  test2 = PE.refl
