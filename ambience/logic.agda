module ambience.logic where

import ambience.unit as unit
open unit hiding (Unit) public

import ambience.void as void
open void hiding (Void) public

open import ambience.sigma public
open import ambience.id public

import ambience.sum as sum
open sum hiding (_+_) public

open import ambience.negation public

open import Agda.Primitive

⊤ : Set
⊤ = unit.Unit

⊥ : Set
⊥ = void.Void

∃ : {i j : _} {A : Set i} → (A → Set j) → Set (i ⊔ j)
∃ B = Σ _ B

syntax ∃ (λ x → B) = ∃[ x ] B

∃! : {i j : _} {A : Set i} → (A → Set j) → Set (i ⊔ j)
∃! B = Σ! _ B

syntax ∃! (λ x → B) = ∃![ x ] B

_&_ : {i j : _} → Set i → Set j → Set (i ⊔ j)
P & Q = P × Q

_∨_ : {i j : _} → Set i → Set j → Set (i ⊔ j)
P ∨ Q = P sum.+ Q

_⇔_ : {i j : _} → Set i → Set j → Set (i ⊔ j)
P ⇔ Q = (P → Q) & (Q → P)
