module Nat where

  open import Reasoning.Equality
  open import Reasoning.Equational
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  succ a + b = succ (a + b)
