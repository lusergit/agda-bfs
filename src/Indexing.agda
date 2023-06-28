module Indexing where
  open import Data.Fin using (Fin; zero; suc)
  open import Data.Nat.Base using (ℕ; _<_)

  data Index : {n : ℕ} → Fin n → Set where
    𝕚 : {m : ℕ} → (n : ℕ) → (x : Fin m) → (n < m) → Index x
