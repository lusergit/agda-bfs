module Tests where
  open import Djikstra
  open import UndirGraph
  open import Matrix
  open import Presence
  import Data.Vec.Base as V
  open V using (Vec; _∷_; []; toList)
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

  adj-l-0 : Vec 𝔹 7
  adj-l-0 = V.head tree1

  adj-l-1 : Vec 𝔹 7
  adj-l-1 = V.head (V.tail tree1)

  -- neighbors of the first node are 1 and 2
  _ : (neighbors adj-l-0) ≡ ((Fin.suc (Fin.zero {5})) ∷ (Fin.suc (Fin.suc (Fin.zero {4}))) ∷ [])
  _ = refl

  -- filtering 0 from the neighbors of 1 leaves with 3 and 4
  _ : (filter-list (neighbors adj-l-1) ((Fin.zero {6}) ∷ [])) ≡
    ((Fin.suc (Fin.suc (Fin.suc (Fin.zero {3})))) ∷
    (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero {2}))))) ∷
    [])
  _ = refl

  _ : (bfs tree1 (Fin.zero {6}) (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero {0})))))))) ≡ (0 ∷ 2 ∷ 6 ∷ [])
  _ = refl
