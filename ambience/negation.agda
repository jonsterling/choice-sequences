module ambience.negation where

open import ambience.void

¬_ : {a : _} → Set a → Set a
¬ A = A → Void
