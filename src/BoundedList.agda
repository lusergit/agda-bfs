module BoundedList where

  open import Data.Nat.Base
  open import Data.Fin.Base using (Fin; zero; suc)

  -- List of max length
  data List (A : Set) : {n : ℕ} → Fin n → Set where
    []  : {n : ℕ} → List A (zero {n})
    _∷_ :  {n : ℕ} {m : Fin n} → A → List A m → List A (Fin.suc m)
