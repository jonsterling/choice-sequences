module spread where

open import choice-sequence
open import naturals
open import negation
open import list
open import sigma
open import sum
open import unit
open import void

PreSpreadLaw : Set₁
PreSpreadLaw = ℕ list → Set

record is-spread-law (admit : PreSpreadLaw) : Set where
  field
    admit-empty : admit []
    admit-^ : (u : ℕ list) → admit u → Σ[ k ∶ ℕ ] admit (u ^ k)
    admit-≼ : (u v : ℕ list) → u ≼ v → admit u → admit v
    admit-dec : (u : ℕ list) → (admit u) + (¬ admit u)

Spread : Set₁
Spread = Σ PreSpreadLaw is-spread-law

universal-spread : Spread
universal-spread = (λ u → Unit) , record
  { admit-empty = ⟨⟩
  ; admit-^ = λ u _ → ze , ⟨⟩
  ; admit-≼ = λ u v _ _ → ⟨⟩
  ; admit-dec = λ u → inl ⟨⟩
  }

prefix : ChoiceSequence → ℕ list → Set
prefix α u = (n : ℕ) (p : n < ∣ u ∣) → α n (u [ n ])

_∈_ : ChoiceSequence → Spread → Set
α ∈ (s , _) = (u : ℕ list) → prefix α u → s u

