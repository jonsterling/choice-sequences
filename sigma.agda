module sigma where

open import Agda.Primitive
open import id

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

_×_ : {a b : _} (A : Set a) (B : Set b) → Set _
A × B = Σ A λ _ → B

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B 

Σ! : {a b : _} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Σ! A B = Σ[ x ∶ A ] (B x × ((y : A) → B y → x == y))

syntax Σ! A (λ x → B) = Σ![ x ∶ A ] B
