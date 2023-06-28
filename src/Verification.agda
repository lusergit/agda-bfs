open import Presence
open import Data.List

module Verification
  (A : Set)                     -- path length
  (_≤_ : A → A → Set)           -- length comparison witnesses
  (cmp? : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  open import Bfs
