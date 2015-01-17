module choice-sequence where

open import naturals
open import sigma

ChoiceSequence : Set₁
ChoiceSequence = ℕ → ℕ → Set

is-lawlike : ChoiceSequence → Set
is-lawlike α = (n : ℕ) → Σ![ m ∶ ℕ ] α n m

compute-sequence : {α : ChoiceSequence} → is-lawlike α → ℕ → ℕ
compute-sequence lawlike n with lawlike n
compute-sequence lawlike n | m , _ = m


