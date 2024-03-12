{-# OPTIONS --without-K --safe #-}

open import Categories.Category

open import Categories.Diagram.Limit
open import Categories.Diagram.Colimit
open import Categories.Category.Finite.Fin.Construction.Discrete
open import Categories.Category.Lift
open import Categories.Functor.Core
open import Categories.Category.Construction.Cocones

module Categories.Object.Initial.Colimit {o ℓ e} (C : Category o ℓ e) where

open module C = Category C

open import Categories.Object.Initial C

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ (Discrete 0)) C} where
  colimit⇒⊥ : Colimit F → Initial
  colimit⇒⊥ L = record
    { ⊥        = coapex
    ; ⊥-is-initial = record
      { !        = rep record
        { coapex = record
          { ψ       = λ ()
          ; commute = λ { {()} }
          }
        }
      ; !-unique = λ f → initial.!-unique record
        { arr     = f
        ; commute = λ { {()} }
        }
      }
    }
    where open Colimit L

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ (Discrete 0)) C} where

  ⊥⇒colimit : Initial → Colimit F
  ⊥⇒colimit t = record
    { initial = record
      { ⊥        = record
        { N    = ⊥
        ; coapex = record
          { ψ       = λ ()
          ; commute = λ { {()} }
          }
        }
      ; ⊥-is-initial = record
        { !        = λ {K} →
          let open Cocone F K
          in record
          { arr     = !
          ; commute = λ { {()} }
          }
        ; !-unique = λ f →
          let module f = Cocone⇒ F f
          in !-unique f.arr
        }
      }
    }
    where open Initial t
