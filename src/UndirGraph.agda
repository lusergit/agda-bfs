module UndirGraph where
  open import Matrix
  open import Data.Nat.Base
  open import Presence
  open import Data.Fin.Base using (Fin; zero; suc; fromℕ; toℕ; inject≤; fromℕ<)
  import Data.Vec.Base as V
  open V using (Vec; _∷_; [])

  graph[_] : ℕ → Set
  graph[ n ] = Matrix 𝔹 n n

  indx : (n : ℕ) → Set
  indx n = Fin (ℕ.suc n)
  
