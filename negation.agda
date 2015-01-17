module negation where

open import void

¬_ : {a : _} → Set a → Set a
¬ A = A → Void
