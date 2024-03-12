{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Lift
open import Categories.Category.Finite.Fin.Construction.Discrete
open import Categories.Functor.Core

module Categories.Diagram.Empty {o ℓ e} (C : Category o ℓ e) where

-- maybe (liftC o′ ℓ′ e′ (Discrete 0)) should be Categories.Category.Empty so this does not depend on liftC
empty : ∀ o′ ℓ′ e′ → Functor (liftC o′ ℓ′ e′ (Discrete 0)) C
empty _ _ _ = record
  { F₀           = λ ()
  ; F₁           = λ { {()} }
  ; identity     = λ { {()} }
  ; homomorphism = λ { {()} }
  ; F-resp-≈     = λ { {()} }
  }
