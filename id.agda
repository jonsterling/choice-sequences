module id where

data _==_ {a} {A : Set a} (M : A) : A → Set a where
  refl : M == M


{-# BUILTIN EQUALITY _==_ #-}
