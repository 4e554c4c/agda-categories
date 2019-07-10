{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Defines the following properties of a Category:
-- 1. BinaryProducts -- for when a Category has all Binary Products
-- 2. FiniteProducts -- for when a Category has all Products

module Categories.Object.BinaryProducts {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product using (Σ; _,_; uncurry)

open Category 𝒞
open HomReasoning

open import Categories.Object.Terminal 𝒞
open import Categories.Object.Product 𝒞
open import Categories.Morphism 𝒞
open import Categories.Square 𝒞

open import Categories.Functor.Bifunctor renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym; trans; _≅_)

private
  variable
    A B C D X Y Z : Obj
    f f′ g g′ h i : A ⇒ B

record BinaryProducts : Set (o ⊔ ℓ ⊔ e) where

  infixr 5 _×_
  infix 8 _⁂_
  infix 10 ⟨_,_⟩

  field
    product : ∀ {A B} → Product A B

  _×_ : Obj → Obj → Obj
  A × B = Product.A×B (product {A} {B})

  ×-comm : A × B ≅ B × A
  ×-comm = Commutative product product

  ×-assoc : X × Y × Z ≅ (X × Y) × Z
  ×-assoc = Associative product product product product

  -- Convenience!
  π₁ : A × B ⇒ A
  π₁ = Product.π₁ product

  π₂ : A × B ⇒ B
  π₂ = Product.π₂ product

  ⟨_,_⟩ : X ⇒ A → X ⇒ B → X ⇒ A × B
  ⟨_,_⟩ = Product.⟨_,_⟩ product

  _⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
  f ⁂ g = [ product ⇒ product ] f × g

  commute₁ : π₁ ∘ ⟨ f , g ⟩ ≈ f
  commute₁ = Product.project₁ product

  commute₂ : π₂ ∘ ⟨ f , g ⟩ ≈ g
  commute₂ = Product.project₂ product

  unique :  π₁ ∘ h ≈ f → π₂ ∘ h ≈ g → ⟨ f , g ⟩ ≈ h
  unique = Product.unique product

  assocˡ : (A × B) × C ⇒ A × B × C
  assocˡ = _≅_.to ×-assoc

  assocʳ : A × B × C ⇒ (A × B) × C
  assocʳ = _≅_.from ×-assoc

  assocʳ∘assocˡ : assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
  assocʳ∘assocˡ = Iso.isoʳ (_≅_.iso ×-assoc)

  assocˡ∘assocʳ : assocˡ {A}{B}{C} ∘ assocʳ {A}{B}{C} ≈ id
  assocˡ∘assocʳ = Iso.isoˡ (_≅_.iso ×-assoc)

  g-η : ⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≈ f
  g-η = Product.g-η product

  η : ⟨ π₁ , π₂ ⟩ ≈ id {A × B}
  η = Product.η product

  ⟨⟩-cong₂ : f ≈ f′ → g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ = Product.⟨⟩-cong₂ product

  ⟨⟩-congʳ : f ≈ f′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g ⟩
  ⟨⟩-congʳ pf = ⟨⟩-cong₂ pf refl
  
  ⟨⟩-congˡ : g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f , g′ ⟩
  ⟨⟩-congˡ pf = ⟨⟩-cong₂ refl pf
    
  swap : A × B ⇒ B × A
  swap = ⟨ π₂ , π₁ ⟩

  -- TODO: this is probably harder to use than necessary because of this definition. Maybe make a version
  -- that doesn't have an explicit id in it, too?
  first : A ⇒ B → A × C ⇒ B × C
  first f = f ⁂ id

  second : C ⇒ D → A × C ⇒ A × D
  second g = id ⁂ g

  -- Just to make this more obvious
  π₁∘⁂ : π₁ ∘ (f ⁂ g) ≈ f ∘ π₁
  π₁∘⁂ {f = f} {g} = commute₁

  π₂∘⁂ : π₂ ∘ (f ⁂ g) ≈ g ∘ π₂
  π₂∘⁂ {f = f} {g} = commute₂

  ⁂-cong₂ : f ≈ g → h ≈ i → f ⁂ h ≈ g ⁂ i
  ⁂-cong₂ = [ product ⇒ product ]×-cong₂

  ⁂∘⟨⟩ : (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g ∘ g′ ⟩
  ⁂∘⟨⟩ = [ product ⇒ product ]×∘⟨⟩

  first∘⟨⟩ : first f ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ = [ product ⇒ product ]×id∘⟨⟩

  second∘⟨⟩ : second g ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ = [ product ⇒ product ]id×∘⟨⟩

  ⁂∘⁂ : (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
  ⁂∘⁂ = [ product ⇒ product ⇒ product ]×∘×

  ⟨⟩∘ : ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
  ⟨⟩∘ = sym (unique (trans (sym assoc) (∘-resp-≈ˡ commute₁)) (trans (sym assoc) (∘-resp-≈ˡ commute₂)))

  first∘first : ∀ {C} → first {C = C} f ∘ first g ≈ first (f ∘ g)
  first∘first = [ product ⇒ product ⇒ product ]×id∘×id

  second∘second : ∀ {A} → second {A = A} f ∘ second g ≈ second (f ∘ g)
  second∘second = [ product ⇒ product ⇒ product ]id×∘id×

  first↔second : first f ∘ second g ≈ second g ∘ first f
  first↔second = [ product ⇒ product , product ⇒ product ]first↔second

  swap∘⟨⟩ : swap ∘ ⟨ f , g ⟩ ≈ ⟨ g , f ⟩
  swap∘⟨⟩ {f = f} {g = g} = begin
    ⟨ π₂ , π₁ ⟩ ∘ ⟨ f , g ⟩             ≈⟨ ⟨⟩∘ ⟩
    ⟨ π₂ ∘ ⟨ f , g ⟩ , π₁ ∘ ⟨ f , g ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ commute₂ commute₁ ⟩
    ⟨ g , f ⟩                           ∎

  swap∘⁂ : swap ∘ (f ⁂ g) ≈ (g ⁂ f) ∘ swap
  swap∘⁂ {f = f} {g = g} = begin
    swap ∘ (f ⁂ g)      ≈⟨ swap∘⟨⟩ ⟩
    ⟨ g ∘ π₂ , f ∘ π₁ ⟩ ≈⟨ sym ⁂∘⟨⟩ ⟩
    (g ⁂ f) ∘ swap      ∎

  swap∘swap : (swap {A}{B}) ∘ (swap {B}{A}) ≈ id
  swap∘swap = trans swap∘⟨⟩ η

  assocʳ∘⟨⟩ : assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈ ⟨ ⟨ f , g ⟩ , h ⟩
  assocʳ∘⟨⟩ {f = f} {g = g} {h = h} = begin
    assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈⟨ ⟨⟩∘ ⟩
    ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    , (π₂ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ⟩                          ≈⟨ ⟨⟩-cong₂ ⟨⟩∘ (pullʳ commute₂) ⟩
    ⟨ ⟨ π₁        ∘ ⟨ f , ⟨ g , h ⟩ ⟩
      , (π₁ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
      ⟩
    , π₂ ∘ ⟨ g , h ⟩
    ⟩                          ≈⟨ ⟨⟩-cong₂ (⟨⟩-cong₂ commute₁
                                                     (trans (pullʳ commute₂) commute₁))
                                           commute₂ ⟩
    ⟨ ⟨ f , g ⟩ , h ⟩          ∎

  assocˡ∘⟨⟩ : assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩ ≈ ⟨ f , ⟨ g , h ⟩ ⟩
  assocˡ∘⟨⟩ {f = f} {g = g} {h = h} = begin
    assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩          ≈⟨ sym (refl ⟩∘⟨ assocʳ∘⟨⟩) ⟩
    assocˡ ∘ assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈⟨ cancelˡ assocˡ∘assocʳ ⟩
    ⟨ f , ⟨ g , h ⟩ ⟩                   ∎

  assocʳ∘⁂ : assocʳ ∘ (f ⁂ (g ⁂ h)) ≈ ((f ⁂ g) ⁂ h) ∘ assocʳ
  assocʳ∘⁂ {f = f} {g = g} {h = h} =
    begin
      assocʳ ∘ (f ⁂ (g ⁂ h))
    ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ ⟨⟩∘ ⟩
      assocʳ ∘ ⟨ f ∘ π₁ , ⟨ (g ∘ π₁) ∘ π₂ , (h ∘ π₂) ∘ π₂ ⟩ ⟩
    ≈⟨ assocʳ∘⟨⟩ ⟩
      ⟨ ⟨ f ∘ π₁ , (g ∘ π₁) ∘ π₂ ⟩ , (h ∘ π₂) ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (⟨⟩-congˡ assoc) assoc ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈˘⟨ ⟨⟩-congʳ ⁂∘⟨⟩ ⟩
      ⟨ (f ⁂ g) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈˘⟨ ⁂∘⟨⟩ ⟩
      ((f ⁂ g) ⁂ h) ∘ assocʳ
    ∎

  assocˡ∘⁂ : assocˡ ∘ ((f ⁂ g) ⁂ h) ≈ (f ⁂ (g ⁂ h)) ∘ assocˡ
  assocˡ∘⁂ {f = f} {g = g} {h = h} =
    begin
      assocˡ ∘ ((f ⁂ g) ⁂ h)
    ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      assocˡ ∘ ⟨ ⟨ (f ∘ π₁) ∘ π₁ , (g ∘ π₂) ∘ π₁ ⟩ , h ∘ π₂ ⟩
    ≈⟨ assocˡ∘⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ (g ∘ π₂) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc (⟨⟩-congʳ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ g ∘ π₂ ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈˘⟨ ⟨⟩-congˡ ⁂∘⟨⟩ ⟩
      ⟨ f ∘ π₁ ∘ π₁ , (g ⁂ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈˘⟨ ⁂∘⟨⟩ ⟩
      (f ⁂ (g ⁂ h)) ∘ assocˡ
    ∎

  -×- : Bifunctor 𝒞 𝒞 𝒞
  -×- = record
    { F₀           = uncurry _×_
    ; F₁           = uncurry _⁂_
    ; identity     = id×id product
    ; homomorphism = sym ⁂∘⁂
    ; F-resp-≈     = uncurry [ product ⇒ product ]×-cong₂
    }

  -×_ : Obj → Functor 𝒞 𝒞
  -×_ = appʳ -×-

  _×- : Obj → Functor 𝒞 𝒞
  _×- = appˡ -×-

record FiniteProducts : Set (o ⊔ ℓ ⊔ e) where
  field
    terminal : Terminal
    products : BinaryProducts

  module terminal = Terminal terminal
  module products = BinaryProducts products
  open terminal public
  open products public

  ⊤×A≅A : ⊤ × A ≅ A
  ⊤×A≅A = record
    { from = π₂
    ; to   = ⟨ ! , id ⟩
    ; iso  = record
      { isoˡ = begin
        ⟨ ! , id ⟩ ∘ π₂ ≈˘⟨ unique !-unique₂ (cancelˡ commute₂) ⟩
        ⟨ π₁ , π₂ ⟩     ≈⟨ η ⟩
        id              ∎
      ; isoʳ = commute₂
      }
    }

  A×⊤≅A : A × ⊤ ≅ A
  A×⊤≅A = record
    { from = π₁
    ; to   = ⟨ id , ! ⟩
    ; iso  = record
      { isoˡ = begin
        ⟨ id , ! ⟩ ∘ π₁ ≈˘⟨ unique (cancelˡ commute₁) !-unique₂ ⟩
        ⟨ π₁ , π₂ ⟩     ≈⟨ η ⟩
        id              ∎
      ; isoʳ = commute₁
      }
    }

  ⊤×--id : NaturalIsomorphism (⊤ ×-) idF
  ⊤×--id = record
    { F⇒G = record
      { η       = λ _ → π₂
      ; commute = λ _ → commute₂
      }
    ; F⇐G = record
      { η       = λ _ → ⟨ ! , id ⟩
      ; commute = λ f → begin
        ⟨ ! , id ⟩ ∘ f                                     ≈⟨ ⟨⟩∘ ⟩
        ⟨ ! ∘ f , id  ∘ f ⟩                                ≈⟨ ⟨⟩-cong₂ (sym (!-unique _)) identityˡ ⟩
        ⟨ ! , f ⟩                                          ≈˘⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
        ⟨ id ∘ ! , f ∘ id ⟩                                ≈˘⟨ ⟨⟩-cong₂ (pullʳ commute₁) (pullʳ commute₂) ⟩
        ⟨ (id ∘ π₁) ∘ ⟨ ! , id ⟩ , (f ∘ π₂) ∘ ⟨ ! , id ⟩ ⟩ ≈˘⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ π₁ , f ∘ π₂ ⟩ ∘ ⟨ ! , id ⟩                  ∎
      }
    ; iso = λ _ → _≅_.iso ⊤×A≅A
    }

  -×⊤-id : NaturalIsomorphism (-× ⊤) idF
  -×⊤-id = record
    { F⇒G = record
      { η       = λ _ → π₁
      ; commute = λ _ → commute₁
      }
    ; F⇐G = record
      { η       = λ _ → ⟨ id , ! ⟩
      ; commute = λ f → begin
        ⟨ id , ! ⟩ ∘ f                                     ≈⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ f , ! ∘ f ⟩                                 ≈⟨ ⟨⟩-cong₂ identityˡ (sym (!-unique _)) ⟩
        ⟨ f , ! ⟩                                          ≈˘⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟩
        ⟨ f ∘ id , id ∘ ! ⟩                                ≈˘⟨ ⟨⟩-cong₂ (pullʳ commute₁) (pullʳ commute₂) ⟩
        ⟨ (f ∘ π₁) ∘ ⟨ id , ! ⟩ , (id ∘ π₂) ∘ ⟨ id , ! ⟩ ⟩ ≈˘⟨ ⟨⟩∘ ⟩
        ⟨ f ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ id , ! ⟩                  ∎
      }
    ; iso = λ _ → _≅_.iso A×⊤≅A
    }
