module finite-sequence where

open import ambience.unit
open import ambience.id
open import ambience.sigma

import ambience.naturals as ℕ

import choice-sequence as cs

data t : Set where
  ⟨⟩ : t
  _^_ : t → ℕ.t → t
infixl 5 _^_

∣_∣ : t → ℕ.t
∣ ⟨⟩ ∣ = 0
∣ u ^ _ ∣ = ℕ.su ∣ u ∣

at : (u : t) (i : ℕ.t) → {{_ : i ℕ.< ∣ u ∣}} → ℕ.t
at ⟨⟩ ℕ.ze {{()}}
at ⟨⟩ (ℕ.su i) {{()}}
at (u ^ x) .(∣ u ∣) {{ℕ.lt-su}} = x
at (u ^ x) _ {{ℕ.lt-tr p}} = at u _ {{p}}

_[_] : (u : t) (i : ℕ.t) → {{_ : i ℕ.< ∣ u ∣}} → ℕ.t
_[_] = at

_*_ : t → t → t
u * ⟨⟩ = u
u * (v ^ x) = (u * v) ^ x

_≼_ : t → t → Set
v ≼ u = Σ[ w ∶ t ] v == (u * w)

_∈_ : cs.t → t → Set
_∈_ = go 0
  where
    go : ℕ.t → cs.t → t → Set
    go i α ⟨⟩ = Unit
    go i α (u ^ n) = α i n × go (ℕ.su i) α u
