module Tests where
  open import Bfs using (neighbors; filter-list; bfs-traverse; bfs; bfs')
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
  _ : (neighbors adj-l-0) ≡ ((suc (zero {5})) ∷ (suc (suc (zero {4}))) ∷ [])
  _ = refl

  -- filtering 0 from the neighbors of 1 leaves with 3 and 4
  _ : (filter-list (neighbors adj-l-1) (zero {6} ∷ [])) ≡
    (suc (suc (suc (zero {3}))) ∷      -- 3
    suc (suc (suc (suc (zero {2})))) ∷ -- 4
    [])
  _ = refl

  -- bfs-traverse returns a prefix visit of the binary tree
  _ : (bfs-traverse tree1 (zero {6})) ≡
    (zero ∷                                      -- 0
    suc zero ∷                                   -- 1
    suc (suc zero) ∷                             -- 2
    suc (suc (suc zero)) ∷                       -- 3
    suc (suc (suc (suc zero))) ∷                 -- 4
    suc (suc (suc (suc (suc zero)))) ∷           -- 5
    suc (suc (suc (suc (suc (suc zero))))) ∷ []) -- 6
  _ = refl

  
  -- BFS returns the minimal path between two nodes
  _ : (bfs tree1 (zero {6}) (suc (suc (suc (suc (suc (suc (zero {0})))))))) ≡
    (zero {6} ∷                                        -- 0
    suc (suc (zero {4})) ∷                             -- 2
    suc (suc (suc (suc (suc (suc (zero {0})))))) ∷ []) -- 6
  _ = refl

  z : indx 6
  z = (zero {6})

  sx : indx 6
  sx = (suc (suc (suc (suc (suc (suc (zero {0})))))))

  -- _ : 
