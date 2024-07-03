{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category

module example {ℓ} (P C D : Category ℓ ℓ ℓ) where

open import Categories.Category.Product renaming (Product to _×ᶜ_)
open import Categories.Diagram.End renaming (End to ∫)
open import Categories.Functor
open import Categories.Diagram.End.Instances.NaturalTransformation
open import Categories.Diagram.End.Parameterized renaming (EndF to ⨏)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom

module _ (F : Functor (P ×ᶜ ((Category.op C) ×ᶜ C)) D) (G : Functor P D) {ω : ∀ X → ∫ (appˡ F X)} where
  private
    module G = Functor G
    ⨏F = (⨏ F) {ω}

  example : ∫ (Hom[ D ][-,-] ∘F (G.op ⁂ ⨏F))
  example = NTs-are-End G ⨏F
