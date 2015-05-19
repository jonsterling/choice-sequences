module ambience.naturals where

open import ambience.sum
open import ambience.id

data t : Set where
  ze : t
  su : t → t

{-# BUILTIN NATURAL t #-}

data _<_ : t → t → Set where
  lt-su : {m : _} → m < su m
  lt-tr : {m n : _} → m < n → m < (su n)

_>_ : t → t → Set
m > n = n < m

_≥_ : t → t → Set
m ≥ n = (m > n) + (m == n)

_≤_ : t → t → Set
m ≤ n = (m < n) + (m == n)

<-trans : {m n k : t} → m < n → n < k → m < k
<-trans lt-su lt-su = lt-tr lt-su
<-trans lt-su (lt-tr q) = lt-tr (<-trans lt-su q)
<-trans (lt-tr p) lt-su = lt-tr (lt-tr p)
<-trans (lt-tr p) (lt-tr q) = lt-tr (<-trans (lt-tr p) q)

<-cancel-su : {m n : t} → su m < su n → m < n
<-cancel-su lt-su = lt-su
<-cancel-su (lt-tr p) = <-trans lt-su p
