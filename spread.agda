module spread where

import ambience.naturals as ℕ
open import ambience.logic
import choice-sequence as cs 
import finite-sequence as fs ; open fs hiding (t; _∈_)

law : Set₁
law = fs.t → Set

record spr (s : law) : Set where
  field
    spr-⟨⟩ : s ⟨⟩
    spr-^ : (u : fs.t) → s u → ∃[ k ] s (u ^ k)
    spr-≼ : (u v : fs.t) → u ≼ v → s u → s v
    spr-dec : (u : fs.t) → s u ∨ (¬ s u)

t : Set₁
t = Σ law spr

universal : t
universal = (λ x → ⊤) , record
  { spr-⟨⟩ = ⟨⟩
  ; spr-^ = λ u _ → ℕ.ze , ⟨⟩
  ; spr-≼ = λ u v _ _ → ⟨⟩
  ; spr-dec = λ u → inl ⟨⟩
  }

∀< : (n : ℕ.t) → ((i : ℕ.t) {{_ : i ℕ.< n}} → Set) → Set
∀< n φ = ∀ i → (_ : i ℕ.< n) → φ i

∃< : (n : ℕ.t) → ((i : ℕ.t) {{_ : i ℕ.< n}} → Set) → Set
∃< n φ = ∃[ i ] Σ[ _ ∶ i ℕ.< n ] φ i

syntax ∀< n (λ i → φ) = ∀[ i < n ] φ
syntax ∃< n (λ i → φ) = ∃[ i < n ] φ

-- The full n-ary spread
full-spr : ℕ.t → t → Set
full-spr n (s , is-law) =
  ∀ u → (s u ⇔ (∀[ i < ∣ u ∣ ] u [ i ] ℕ.< n))
      & ((¬ s u) ⇔ (∃[ i < ∣ u ∣ ] u [ i ] ℕ.≥ n))

-- a choice sequence is in a spread is every one of its prefixes is admitted
_∈_ : cs.t → law → Set
α ∈ s = ∀ u → α fs.∈ u → s u
