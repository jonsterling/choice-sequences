module choice-sequence where

import ambience.naturals as ℕ
open import ambience.logic

t : Set₁
t = ℕ.t → ℕ.t → Set

is-lawlike : t → Set
is-lawlike α = ∀ n → ∃![ m ] α n m

compute-sequence : {α : t} → is-lawlike α → ℕ.t → ℕ.t
compute-sequence lawlike n with lawlike n
compute-sequence lawlike n | m , _ = m
