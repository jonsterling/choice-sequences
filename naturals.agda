module naturals where

open import sum
open import id

data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data _<_ : ℕ → ℕ → Set where
  lt-su : {m : ℕ} → m < su m
  lt-tr : {m n : ℕ} → m < n → m < (su n)

_>_ : ℕ → ℕ → Set
m > n = n < m

_≥_ : ℕ → ℕ → Set
m ≥ n = (m > n) + (m == n)

_≤_ : ℕ → ℕ → Set
m ≤ n = (m < n) + (m == n)


<-trans : {m n k : ℕ} → m < n → n < k → m < k
<-trans lt-su lt-su = lt-tr lt-su
<-trans lt-su (lt-tr q) = lt-tr (<-trans lt-su q)
<-trans (lt-tr p) lt-su = lt-tr (lt-tr p)
<-trans (lt-tr p) (lt-tr q) = lt-tr (<-trans (lt-tr p) q)

<-cancel-su : {m n : ℕ} → su m < su n → m < n
<-cancel-su lt-su = lt-su
<-cancel-su (lt-tr p) = <-trans lt-su p
