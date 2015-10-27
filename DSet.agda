module DSet where
  open import Relation.Nullary
  open import Relation.Binary
  open import Data.Sum
  open import Data.Product
  open import Data.Empty
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality
  open import Function

  data DSet (S : Set) : Set₁ where
    D : (F : S → Set) → (∀ x → Dec (F x)) → DSet S

  module _ {S : Set}⦃ dec : Decidable (_≡_ {A = S}) ⦄ where

    _ᶜ : DSet S → DSet S
    (D S d) ᶜ = D (λ x → ¬ S x) (λ x → case d x of λ { (yes p) → no (λ x → x p); (no p) → yes p })

    _∈_ : S → DSet S → Set
    x ∈ (D S d) = S x

    ∅ : DSet S
    ∅ = D ( λ _ → ⊥)  ( λ x → no id)

    U : DSet S
    U = D ( λ _ → ⊤) (λ x → yes tt)

    _∪_ : DSet S → DSet S → DSet S
    _∪_ (D S d ) (D S′ d′ ) = D ( λ x → S x ⊎ S′ x) (λ x → d x ⊎-dec d′ x )
       where open import Relation.Nullary.Sum

    _∩_ : DSet S → DSet S → DSet S
    _∩_ (D S d ) (D S′ d′ ) = D ( λ x → S x × S′ x) (λ x → d x ×-dec d′ x )
       where open import Relation.Nullary.Product

    infixr 6 _∩_
    infixr 5 _∪_
    infixr 4 _∈_
    infix 4 _≈_ _⊆_

    _∉_ : S → DSet S → Set
    x ∉ (D S d )  = ¬ S x


    lem : {X : DSet S}{x : S} → x ∈ (X ∪ X ᶜ)
    lem {X = (D S′ d)}{x} with d x
    ... | yes p = inj₁ p
    ... | no  p = inj₂ p


    ⟪_⟫ :  S → DSet S
    ⟪_⟫ x = D (λ y → x ≡ y) (λ y → dec x y)

    _⊆_ :  DSet S → DSet S → Set
    P ⊆ Q = ∀ x → x ∈ P → x ∈ Q

    record _≈_  (P Q : DSet S) : Set where
      constructor equiv
      field subset₁ : P ⊆ Q
      field subset₂ : Q ⊆ P



    ∪-comm : {X Y : DSet S} → X ∪ Y ≈ Y ∪ X
    ∪-comm {D _ _} {D _ _} = equiv (λ _ → λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x}) (λ _ → λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x})

    ∪-assoc : { X Y Z : DSet S} → (X ∪ Y) ∪ Z ≈ X ∪ Y ∪ Z
    ∪-assoc {D _ _} {D _ _} {D _ _} = equiv (λ _ → λ { (inj₁ (inj₁ x)) → inj₁ x; (inj₁ (inj₂ x)) → inj₂ (inj₁ x); (inj₂ x) → inj₂ (inj₂ x)})
                                            (λ _ → λ { (inj₂ (inj₁ x)) → inj₁ (inj₂ x); (inj₂ (inj₂ x)) → inj₂ x; (inj₁ x) → inj₁ (inj₁ x)})

    ∪-distrib : { X Y Z : DSet S} → X ∪ (Y ∩ Z) ≈ (X ∪ Y) ∩ (X ∪ Z)
    ∪-distrib {D _ _} {D _ _} {D _ _} = equiv (λ _ → λ { (inj₁ x) → inj₁ x , inj₁ x ; (inj₂ (x₁ , x₂)) → inj₂ x₁ , inj₂ x₂ })
                                              (λ _ → λ { (inj₁ x , _) → inj₁ x ; (_ , inj₁ x) → inj₁ x ; (inj₂ x , inj₂ x′) → inj₂ (x , x′) })

    ∪-id : {A : DSet S} →  A ∪ ∅ ≈ A
    ∪-id {D _ _} = equiv (λ { _ (inj₁ x) → x; _ (inj₂ b) → ⊥-elim b}) (λ _ → inj₁)

    ∩-comm : {X Y : DSet S} → X ∩ Y ≈ Y ∩ X
    ∩-comm {D _ _} {D _ _} = equiv (λ { _ (a , b) → b , a }) (λ { _ (a , b) → b , a})

    ∩-assoc : { X Y Z : DSet S} → (X ∩ Y) ∩ Z ≈ X ∩ (Y ∩ Z)
    ∩-assoc {D _ _} {D _ _} {D _ _} = equiv (λ { _ ((a , b) , c) → a , b , c})
                                            (λ { _ (a , b , c) → (a , b) , c })
    ∩-distrib : {X Y Z : DSet S} → X ∩ (Y ∪ Z) ≈ (X ∩ Y) ∪ (X ∩ Z)
    ∩-distrib {D _ _} {D _ _} {D _ _} = equiv (λ { _ (a , inj₁ b) → inj₁ (a , b) ; _ (a , inj₂ b) → inj₂ (a , b) })
                                              (λ { _ (inj₁ (a , b)) → a , inj₁ b ; _ (inj₂ (a , b)) → a , inj₂ b})

    ∩-id : {A : DSet S} → A ∩ U ≈ A
    ∩-id {D _ _} = equiv (λ { _ (a , b) → a}) (λ _ x → x , tt)

    ∪-comp : {X : DSet S} → X ∪ X ᶜ ≈ U
    ∪-comp {D a b} = equiv (λ _ _ → tt) (λ x _ → lem {D a b}{x} )

    ∩-comp : {X : DSet S} → X ∩ X ᶜ ≈ ∅
    ∩-comp {D a b} = equiv (λ _ z → proj₂ z (proj₁ z)) (λ _ → λ ())


    ∪-deMorgan : {A B : DSet S} → (A ∪ B) ᶜ ≈ A ᶜ ∩ B ᶜ
    ∪-deMorgan {D _ _} {D _ _} = equiv (λ x n → n ∘ inj₁ , n ∘ inj₂)
                                       (λ x n → λ { (inj₁ x) → proj₁ n x; (inj₂ x) → proj₂ n x })

    ∩-deMorgan : {A B : DSet S} → (A ∩ B) ᶜ ≈ A ᶜ ∪ B ᶜ
    ∩-deMorgan {D a b} {D c d} = equiv (λ x n → help {x} n ) (λ { _ (inj₁ a) → λ z → a (proj₁ z); _ (inj₂ b) → λ z → b (proj₂ z)})
      where help : ∀ {x} → x ∈ (D a b ∩ D c d) ᶜ → x ∈ D a b ᶜ ⊎ x ∈ D c d ᶜ
            help {x} with lem {D a b}{x} | lem {D c d}{x}
            ... | _ | inj₁ q = λ z → inj₁ (λ x₁ → z (x₁ , q))
            ... | inj₂ p | inj₂ q = λ _ → inj₁ p
            ... | inj₁ p | inj₂ q = λ z → inj₂ (λ x₁ → z (p , x₁))

    involution : {A : DSet S} → A ᶜ ᶜ ≈ A
    involution {D a b} = equiv (λ x n → case lem {D a b}{x} of λ { (inj₁ p) → p
                                                                  ; (inj₂ p) → ⊥-elim (n p)
                                                                  })
                               (λ x z z₁ → z₁ z)

    ∅-comp : ∅ ᶜ ≈ U
    ∅-comp = equiv (λ _ _ → tt) (λ _ _ → id)

    U-comp : U ᶜ ≈ ∅
    U-comp = equiv (λ _  z → z tt ) (λ _ z _ → z)

    ≈-sym : ∀{A B : DSet S} → A ≈ B → B ≈ A
    ≈-sym (equiv e₁ e₂) = equiv e₂ e₁

    ≈-refl :  ∀{A : DSet S} → A ≈ A
    ≈-refl = equiv (λ _ x → x) (λ _ x → x)

    ≈-trans : ∀{A B C : DSet S} → A ≈ B → B ≈ C → A ≈ C
    ≈-trans (equiv e₁ e₂) (equiv e₁′ e₂′) = equiv (λ x → e₁′ x  ∘ e₁ x ) (λ x → e₂ x ∘ e₂′ x)

    ≈-equiv : IsEquivalence _≈_
    ≈-equiv = record { refl =  ≈-refl  ; trans = ≈-trans ; sym = ≈-sym }

    ∪-cong : ∀{A A′ B B′} → A ≈ A′ → B ≈ B′ → A ∪ B ≈ A′ ∪ B′
    ∪-cong {D _ _}{D _ _}{D _ _}{D _ _} (equiv e₁ e₁′) (equiv e₂ e₂′)
        = equiv (λ { _ (inj₁ f) → inj₁ (e₁  _ f); _ (inj₂ f′) → inj₂ (e₂  _ f′)})
                (λ { _ (inj₁ f) → inj₁ (e₁′ _ f); _ (inj₂ f′) → inj₂ (e₂′ _ f′)})

    ∩-cong  : ∀{A A′ B B′} → A ≈ A′ → B ≈ B′ → A ∩ B ≈ A′ ∩ B′
    ∩-cong {D _ _}{D _ _}{D _ _}{D _ _} (equiv e₁ e₁′) (equiv e₂ e₂′)
        = equiv (λ { _ (a , b) → e₁ _ a , e₂ _ b}) (λ { _ (a , b) → e₁′ _ a , e₂′ _ b})

    ᶜ-cong : ∀ {A A′} → A ≈ A′ → A ᶜ ≈ A′ ᶜ
    ᶜ-cong {D _ _}{D _ _} (equiv e₁ e₂) = equiv (λ x z x₁ → z (e₂ x x₁)) (λ x z x₁ → z (e₁ x x₁))


    import Level
    dset-setoid : Setoid (Level.suc Level.zero) (Level.zero)
    dset-setoid = record { Carrier = DSet S; _≈_ = _≈_; isEquivalence = ≈-equiv}
    open import Relation.Binary.EqReasoning (dset-setoid) public
    ∪-idem : {X : DSet S} → (X ∪ X) ≈ X
    ∪-idem {X} = begin  X ∪ X                 ≈⟨ ≈-sym ∩-id ⟩
                        (X ∪ X) ∩ U           ≈⟨ ∩-cong ≈-refl (≈-sym ∪-comp) ⟩
                        (X ∪ X) ∩ (X ∪ X ᶜ)   ≈⟨ ≈-sym ∪-distrib ⟩
                        X ∪ (X ∩ X ᶜ)         ≈⟨ ∪-cong ≈-refl ∩-comp ⟩
                        X ∪ ∅                 ≈⟨ ∪-id ⟩
                        X                     ∎

    ∩-idem : {X : DSet S} → (X ∩ X) ≈ X
    ∩-idem {X} = begin X ∩ X               ≈⟨ ≈-sym ∪-id ⟩
                       (X ∩ X) ∪ ∅         ≈⟨ ∪-cong ≈-refl (≈-sym ∩-comp) ⟩
                       (X ∩ X) ∪ (X ∩ X ᶜ) ≈⟨ ≈-sym ∩-distrib ⟩
                       X ∩ (X ∪ X ᶜ)       ≈⟨ ∩-cong ≈-refl ∪-comp ⟩
                       X ∩ U               ≈⟨ ∩-id ⟩
                       X                   ∎


    ∪-dom : {X : DSet S} → X ∪ U ≈ U
    ∪-dom {X} = begin X ∪ U           ≈⟨ ∪-cong ≈-refl (≈-sym ∪-comp) ⟩
                      X ∪ (X ∪ X ᶜ)   ≈⟨ ≈-sym ∪-assoc ⟩
                      (X ∪ X) ∪ X ᶜ   ≈⟨ ∪-cong ∪-idem ≈-refl ⟩
                      X ∪ X ᶜ         ≈⟨ ∪-comp ⟩
                      U              ∎

    ∩-dom : {X : DSet S} → X ∩ ∅ ≈ ∅
    ∩-dom {X} = begin X ∩ ∅         ≈⟨ ∩-cong ≈-refl (≈-sym ∩-comp) ⟩
                      X ∩ (X ∩ X ᶜ) ≈⟨ ≈-sym ∩-assoc ⟩
                      (X ∩ X) ∩ X ᶜ ≈⟨ ∩-cong ∩-idem ≈-refl ⟩
                      X ∩ X ᶜ       ≈⟨ ∩-comp ⟩
                      ∅            ∎

    ∪-dom-≈ : {X Y : DSet S} → X ∪ Y ≈ ∅ → X ≈ ∅ × Y ≈ ∅
    ∪-dom-≈ {D _ _}{D _ _} (equiv e₁ e₂) = (equiv (λ x → e₁ x ∘ inj₁) (λ _ ()))
                                         , (equiv (λ x → e₁ x ∘ inj₂) (λ _ ()))

    ∩-dom-≈ : {X Y : DSet S} → X ∩ Y ≈ U → X ≈ U × Y ≈ U
    ∩-dom-≈ {D _ _}{D _ _} (equiv e₁ e₂) = equiv (λ x _ → tt) (λ x _ → proj₁ (e₂ x tt))
                                         , equiv (λ x _ → tt) (λ x _ → proj₂ (e₂ x tt))

    ∩-absorb : {A B : DSet S} → A ∪ (A ∩ B) ≈ A
    ∩-absorb {A}{B} = begin A ∪ (A ∩ B)       ≈⟨ ∪-cong (≈-sym ∩-id) ≈-refl ⟩
                            (A ∩ U) ∪ (A ∩ B) ≈⟨ ≈-sym ∩-distrib ⟩
                            A ∩ (U ∪ B)       ≈⟨ ∩-cong ≈-refl (≈-trans ∪-comm ∪-dom) ⟩
                            A ∩ U             ≈⟨ ∩-id ⟩
                            A                 ∎

    ∪-absorb : {A B : DSet S} → A ∩ (A ∪ B) ≈ A
    ∪-absorb {A}{B} = begin A ∩ (A ∪ B)        ≈⟨ ∩-cong (≈-sym ∪-id) ≈-refl ⟩
                            (A ∪ ∅) ∩ (A ∪ B)  ≈⟨ ≈-sym ∪-distrib ⟩
                            A ∪ (∅ ∩ B)        ≈⟨ ∪-cong ≈-refl (≈-trans ∩-comm ∩-dom) ⟩
                            A ∪ ∅              ≈⟨ ∪-id ⟩
                            A                  ∎




    _no-alias_ : DSet S → DSet S → Set
    P no-alias Q = (P ∩ Q) ≈ ∅
