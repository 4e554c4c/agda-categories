{-# OPTIONS --without-K #-}

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Product renaming (Product to _×ᶜ_)
open import Categories.Category.Construction.Functors
open import Categories.Category.Construction.TwistedArrow
open import Categories.Category.Equivalence
open import Categories.Category.Equivalence.Preserves
open import Categories.Diagram.Cone
open import Categories.Diagram.End using () renaming (End to ∫)
open import Categories.Diagram.End.Properties --using () renaming (End to ∫)
open import Categories.Diagram.Limit
open import Categories.Diagram.Wedge
open import Categories.Diagram.Wedge.Properties
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
--open import Categories.Functor.Instance.Twisted
import Categories.Morphism as M
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.Dinatural
open import Categories.Object.Terminal as Terminal

import Categories.Category.Construction.Wedges as Wedges
--open import Categories.Object.Terminal

import Categories.Morphism.Reasoning as MR

module Categories.Diagram.End.Fubini {o ℓ e o′ ℓ′ e′ o′′ ℓ′′ e′′}
  {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′ }
  (F : Bifunctor (Category.op C ×ᶜ Category.op D) (C ×ᶜ D) E) where
--open Wedges F
module C = Category C
module D = Category D
module F = Functor F

private
  F′ : Bifunctor (C.op ×ᶜ C) (D.op ×ᶜ D) E
  F′ = F ∘F ((πˡ ∘F πˡ ※ πˡ ∘F πʳ) ※ (πʳ ∘F πˡ ※ πʳ ∘F πʳ))

foo = (∫ (F′ ♯))

module _ {eₚ : ∫ F} {eᵢ₁ : ∫ (F′ ♯)} {eᵢ : ∫ (∫.E eᵢ₁)} where
  open M E

  Fubini : ∫.E eₚ ≅ ∫.E eᵢ
  Fubini = ?

