module list where

open import id
open import naturals
open import sigma

module _ {a} where
  data _list (A : Set a) : Set a where
    [] : A list
    _∷_ : A → A list → A list
  

  module _ {A : Set _} where
    _⋆_ : A list → A list → A list 
    [] ⋆ ys = ys
    (x ∷ xs) ⋆ ys = x ∷ (xs ⋆ ys)

    _^_ : A list → A → A list
    xs ^ x = xs ⋆ (x ∷ [])

    _≼_ : A list → A list → Set _
    ys ≼ xs = Σ[ zs ∶ A list ] ys == (xs ⋆ zs)

    ∣_∣ : A list → ℕ
    ∣ [] ∣ = 0
    ∣ _ ∷ xs ∣ = su ∣ xs ∣

    _[_] : (xs : A list) (i : ℕ) {{_ : i < ∣ xs ∣}} → A
    _[_] [] i {{()}}
    _[_] (x ∷ xs) .(∣ xs ∣) {{lt-su}} = x
    _[_] (x ∷ xs) ze {{lt-tr p}} = x
    _[_] (x ∷ xs) (su m) {{lt-tr p}} = _[_] xs m {{<-cancel-su (lt-tr p)}}
