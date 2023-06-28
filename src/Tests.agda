module Tests where
  open import Djikstra
  open import UndirGraph
  open import Presence
  import Data.Vec.Base as V
  open V using (_∷_; []; toList)
  open import Data.Fin.Base using (Fin; zero; suc; fromℕ; toℕ; inject≤; fromℕ<)
  open import Data.Nat.Base using (ℕ; _<_; s≤s; z≤n)
  open import Reasoning.Equality
  open import Data.List as L using (List; _∷_; [])

  tree1 : graph[ 7 ]
  tree1 = ( O ∷ I ∷ I ∷ O ∷ O ∷ O ∷ O ∷ [])
        ∷ ( I ∷ O ∷ O ∷ I ∷ I ∷ O ∷ O ∷ [])    --          (0)
        ∷ ( I ∷ O ∷ O ∷ O ∷ O ∷ I ∷ I ∷ [])    --         /   \
        ∷ ( O ∷ I ∷ O ∷ O ∷ O ∷ O ∷ O ∷ [])    --        /     \
        ∷ ( O ∷ I ∷ O ∷ O ∷ O ∷ O ∷ O ∷ [])    --     (1)       (2)
        ∷ ( O ∷ O ∷ I ∷ O ∷ O ∷ O ∷ O ∷ [])    --    /   \     /   \
        ∷ ( O ∷ O ∷ I ∷ O ∷ O ∷ O ∷ O ∷ [])    --  (3)   (4) (5)   (6)
        ∷ []
