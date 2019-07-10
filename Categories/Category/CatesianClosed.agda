{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.CatesianClosed {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞

open import Level
open import Function using (_$_)
open import Data.Product using (Σ; _,_; uncurry)

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Category.Catesian 𝒞
open import Categories.Object.Product 𝒞
  hiding (repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)
open import Categories.Object.Exponential 𝒞 hiding (repack)
open import Categories.Morphism 𝒞
open import Categories.Square 𝒞

open HomReasoning

private
  variable
    A B C : Obj
    f g   : A ⇒ B

-- record Exponentials : Set (levelOf 𝒞) where
--   infixl 7 _^_
  
--   field
--     exp : Exponential A B

--   module exp {A B} = Exponential (exp {A} {B})

--   _^_ : Obj → Obj → Obj
--   B ^ A = exp.B^A {A} {B}

--   product : ∀ B A → Product (B ^ A) A
--   product B A = exp.product {A} {B}

--   eval : Product.A×B (product B A) ⇒ B
--   eval = exp.eval

--   λg : Product.A×B (product C A) ⇒ B → C ^ A ⇒ B ^ A
--   λg f = exp.λg exp.product f

--   λ-cong : f ≈ g → λg f ≈ λg g
--   λ-cong eq = exp.λ-cong exp.product eq

--   _×id : (f : B ^ A ⇒ C ^ A) → [[ product B A ]] ⇒ [[ product C A ]]
--   f ×id = [ exp.product ⇒ exp.product ] f ×id

--   β : eval ∘ λg f ×id ≈ f
--   β = exp.β exp.product

--   -^-functor : Obj → Functor 𝒞 𝒞
--   -^-functor A = record
--     { F₀           = _^ A
--     ; F₁           = λ f → λg (f ∘ eval)
--     ; identity     = trans (λ-cong identityˡ) exp.η-id
--     ; homomorphism = exp.λ-unique₂ exp.product homoeq
--     ; F-resp-≈     = λ eq → λ-cong (∘-resp-≈ˡ eq)
--     }
--     where homoeq : eval {A = A} ∘ (λg ((g ∘ f) ∘ eval) ×id) ≈ eval ∘ ((λg (g ∘ eval) ∘ λg (f ∘ eval)) ×id)
--           homoeq {g = g} {f = f} = begin
--             eval ∘ (λg ((g ∘ f) ∘ eval) ×id)               ≈⟨ β ⟩
--             (g ∘ f) ∘ eval                                 ≈⟨ pullʳ (sym β) ⟩
--             g ∘ eval ∘ λg (f ∘ eval) ×id                   ≈⟨ pullˡ (sym β) ⟩
--             (eval ∘ λg (g ∘ eval) ×id) ∘ λg (f ∘ eval) ×id ≈⟨ pullʳ [ exp.product ⇒ exp.product ⇒ exp.product ]×id∘×id ⟩
--             eval ∘ ((λg (g ∘ eval) ∘ λg (f ∘ eval)) ×id)   ∎

-- Catesian closed category
record CatesianClosed : Set (levelOf 𝒞) where
  infixl 7 _^_
  
  field
    catesian : Catesian
    exp      : Exponential A B

  module exp {A B} = Exponential (exp {A} {B})

  _^_ : Obj → Obj → Obj
  B ^ A = exp.B^A {A} {B}

  module catesian = Catesian catesian

  open catesian public

  B^A×A : ∀ B A → Product (B ^ A) A
  B^A×A B A = exp.product {A} {B}

  eval : Product.A×B (B^A×A B A) ⇒ B
  eval = exp.eval

  λg : C × A ⇒ B → C ⇒ B ^ A
  λg f = exp.λg product f

  λ-cong : f ≈ g → λg f ≈ λg g
  λ-cong eq = exp.λ-cong product eq

  _×id : (f : C ⇒ B ^ A) → C × A ⇒ [[ B^A×A B A ]]
  f ×id = [ product ⇒ exp.product ] f ×id

  β : eval ∘ λg f ×id ≈ f
  β = exp.β product

  λ-unique : eval ∘ f ×id ≈ g → f ≈ λg g
  λ-unique = exp.λ-unique product

  λ-unique₂ : eval ∘ f ×id ≈ eval ∘ g ×id → f ≈ g
  λ-unique₂ = exp.λ-unique′ product

  -- the annoying detail is that B^A×A is NOT the same as B ^ A × A, but they are isomorphic.
  -- make some infra so that the latter (which is more intuitive) can be used.
  
  B^A×A-iso : Product.A×B (B^A×A B A) ≅ B ^ A × A
  B^A×A-iso {B = B} {A = A} = record
    { from = repack exp.product product
    ; to   = repack product exp.product
    ; iso  = record
      { isoˡ = begin
        repack product exp.product ∘ repack exp.product product
          ≈⟨ [ exp.product ]⟨⟩∘ ⟩
        [ exp.product ]⟨ π₁ ∘ repack exp.product product , π₂ ∘ repack exp.product product ⟩
          ≈⟨ Product.⟨⟩-cong₂ exp.product project₁ project₂ ⟩
        [ exp.product ]⟨ [ exp.product ]π₁ , [ exp.product ]π₂ ⟩
          ≈⟨ Product.η exp.product ⟩
        id
          ∎
      ; isoʳ = begin
        repack exp.product product ∘ repack product exp.product
          ≈⟨ ⟨⟩∘ ⟩
        ⟨ [ exp.product ]π₁ ∘ repack product exp.product , [ exp.product ]π₂ ∘ repack product exp.product ⟩
          ≈⟨ ⟨⟩-cong₂ (Product.project₁ exp.product) (Product.project₂ exp.product) ⟩
        ⟨ π₁ , π₂ ⟩
          ≈⟨ η ⟩
        id
          ∎
      }
    }

  eval′ : B ^ A × A ⇒ B
  eval′ = eval ∘ to
    where open _≅_ B^A×A-iso

  λ-unique′ : eval′ ∘ (f ⁂ id) ≈ g → f ≈ λg g
  λ-unique′ eq = exp.λ-unique product (⟺ (pullʳ [ product ⇒ product ⇒ exp.product ]repack∘×) ○ eq)

  λ-unique₂′ : eval′ ∘ (f ⁂ id) ≈ eval′ ∘ (g ⁂ id) → f ≈ g
  λ-unique₂′ eq = (λ-unique′ eq) ○ ⟺ (λ-unique′ refl) 

  β′ : eval′ ∘ (λg f ⁂ id) ≈ f
  β′ {f = f} = begin
    eval′ ∘ (λg f ⁂ id) ≈⟨ pullʳ [ product ⇒ product ⇒ exp.product ]repack∘× ⟩
    eval ∘ λg f ×id     ≈⟨ β ⟩
    f                   ∎

  ⊤^A≅⊤ : ⊤ ^ A ≅ ⊤
  ⊤^A≅⊤ = record
    { from = !
    ; to   = λg !
    ; iso  = record
      { isoˡ = λ-unique₂ !-unique₂
      ; isoʳ = ⊤-id _
      }
    }

  A^⊤≅A : A ^ ⊤ ≅ A
  A^⊤≅A = record
    { from = let open _≅_ A×⊤≅A in eval′ ∘ to
    ; to   = let open _≅_ A×⊤≅A in λg from
    ; iso  = record
      { isoˡ = λ-unique₂′ $ begin
        eval′ ∘ ((λg π₁ ∘ eval′ ∘ ⟨ id , ! ⟩) ⁂ id)          ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval′ ∘ ((λg π₁ ⁂ id) ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)) ≈⟨ pullˡ β′ ⟩
        π₁ ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)                     ≈⟨ helper ⟩
        eval′ ∘ (id ⁂ id)                                    ∎
      ; isoʳ = firstid ! $ begin
        ((eval′ ∘ ⟨ id , ! ⟩) ∘ λg π₁) ⁂ id                  ≈˘⟨ first∘first ⟩
        (eval′ ∘ ⟨ id , ! ⟩ ⁂ id) ∘ (λg π₁ ⁂ id)             ≈⟨ helper′ ⟩∘⟨refl ⟩
        (⟨ id , ! ⟩ ∘ eval′) ∘ (λg π₁ ⁂ id)                  ≈⟨ pullʳ β′ ⟩
        ⟨ id , ! ⟩ ∘ π₁                                      ≈⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                                 ≈⟨ ⟨⟩-cong₂ identityˡ !-unique₂ ⟩
        ⟨ π₁ , π₂ ⟩                                          ≈⟨ η ⟩
        id                                                   ∎
      }
    }
    where helper = begin
            π₁ ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)                 ≈⟨ project₁ ⟩
            (eval′ ∘ ⟨ id , ! ⟩) ∘ π₁                        ≈⟨ pullʳ ⟨⟩∘ ⟩
            eval′ ∘ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                     ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ !-unique₂ ⟩
            eval′ ∘ (id ⁂ id)                                ∎
          helper′ = let open _≅_ A×⊤≅A in begin
            (eval′ ∘ ⟨ id , ! ⟩) ⁂ id                        ≈⟨ introˡ isoˡ ⟩
            (⟨ id , ! ⟩ ∘ π₁) ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)  ≈⟨ pullʳ helper ⟩
            ⟨ id , ! ⟩ ∘ (eval′ ∘ (id ⁂ id))                 ≈⟨ refl⟩∘⟨ elimʳ (id×id product) ⟩
            ⟨ id , ! ⟩ ∘ eval′                               ∎

  -- -^- : Bifunctor op 𝒞 𝒞
  -- -^- = record
  --   { F₀           = uncurry _^_
  --   ; F₁           = λ where
  --     (f , g) → {!!}
  --   ; identity     = {!!}
  --   ; homomorphism = {!!}
  --   ; F-resp-≈     = {!!}
  --   }
