-- Djikstra's algorithm
module Djikstra where
  open import Matrix
  import Data.Vec as V
  open V using (Vec)
  open import Presence
  open import Data.Fin.Base using (Fin; zero; suc; fromℕ; toℕ; inject≤; fromℕ<)
  open import Data.List
  open import Data.Nat.Base using (ℕ; _<_; s≤s; _≤_)
  open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

  lemma2 : ∀ (n : ℕ) → ∀ (i : Fin n) → (toℕ i) < ℕ.suc n
  lemma2 (ℕ.suc n) zero = s≤s _≤_.z≤n
  lemma2 (ℕ.suc n) (suc i) = s≤s (lemma2 n i)

  lemma3 : ∀ (n : ℕ) → ∀ (i : Fin n) → toℕ i < n
  lemma3 (ℕ.suc n) zero = s≤s _≤_.z≤n
  lemma3 (ℕ.suc n) (suc i) = s≤s (lemma3 n i)
  
  -- Neightbors : Given a vector rapresenting the adiacency list of a
  -- node returns the indexes of the nodes
  {-# TERMINATING #-}
  neighbors : ∀ {n : ℕ} → Vec 𝔹 (ℕ.suc n) → List (Fin (ℕ.suc n))
  neighbors {n} v = neighbors' v (Data.Fin.Base.fromℕ n) []
    where
    -- pred in Fin n, si dovrebbe sempre poter fare, zero rimane zero
    reduce : ∀ {n : ℕ} → Fin (ℕ.suc n) → Fin (ℕ.suc n)
    reduce zero = zero
    reduce {n} (Fin.suc zero) = zero
    reduce {n} (Fin.suc m) = fromℕ< {toℕ m} {ℕ.suc n} (lemma2 n m)

    neighbors' : ∀ {n : ℕ} → Vec 𝔹 (ℕ.suc n) → Fin (ℕ.suc n) → List (Fin (ℕ.suc n)) → List (Fin (ℕ.suc n))
    neighbors' v Fin.zero l with (V.lookup v Fin.zero)
    ... | I = Fin.zero ∷ l
    ... | O = l
    neighbors' v x l with (V.lookup v x)
    ... | I = neighbors' v (reduce x) (x ∷ l)
    ... | O = neighbors' v (reduce x) l

  _≡?_ : ℕ → ℕ → 𝔹
  ℕ.zero ≡? ℕ.zero = I
  ℕ.zero ≡? ℕ.suc b = O
  ℕ.suc a ≡? ℕ.zero = O
  ℕ.suc a ≡? ℕ.suc b = a ≡? b

  lookup-l : ∀ {n : ℕ} → Fin (ℕ.suc n) → List (Fin (ℕ.suc n)) → 𝔹
  lookup-l x [] = O
  lookup-l x (y ∷ ys) with toℕ x ≡? toℕ y
  ... | I = I
  ... | O = lookup-l x ys

  -- Note : Vectors are explicity non-empty: The size is always n + 1 ∀ n ∈ ℕ.
  filter-list : ∀ {n : ℕ} → List (Fin (ℕ.suc n)) → List (Fin (ℕ.suc n)) → List (Fin (ℕ.suc n))
  filter-list [] m = []
  filter-list (x ∷ xs) ys with lookup-l x ys
  ... | I = filter-list xs ys
  ... | O = x ∷ (filter-list xs ys)

  -- Given a graph (its adiacency matrix) and an index (number of
  -- value at max n), return a list that rapresents the next indexes to see
  {-# TERMINATING #-}
  bfs-traverse : ∀ {n : ℕ} → Matrix 𝔹 (ℕ.suc n) (ℕ.suc n) → Fin (ℕ.suc n) → List (Fin (ℕ.suc n))
  bfs-traverse g f = bfs-traverse' g [ f ] [] [ f ]
    where
    -- Given a graph and a list of already visited node and a list of
    -- successors return the list of next nodes to traverse the graph
    bfs-traverse' : ∀ {n : ℕ}
      → Matrix 𝔹 (ℕ.suc n) (ℕ.suc n)
      → List (Fin (ℕ.suc n))
      → List (Fin (ℕ.suc n))
      → List (Fin (ℕ.suc n))
      → List (Fin (ℕ.suc n))
    bfs-traverse' G L Q σ with Q
    ... | [] = L
    ... | x ∷ xs with filter-list (neighbors (row G x)) σ
    ... | [] = bfs-traverse' G xs (L ++ [ x ]) σ
    ... | y ∷ ys = bfs-traverse' G (xs ++ ys) (L ++ [ x ]) (σ ++ ys)

  constvec : {A : Set} → (n : ℕ) → (val : A) → Vec A n
  constvec ℕ.zero val = V.[]
  constvec (ℕ.suc n) val = val V.∷ (constvec n val)

  -- bfs itself: Given a graph, a starting index and a finish index,
  -- return the shortest path (a list of node indexes) between the
  -- starting point and the finish point
  {-# TERMINATING #-}
  bfs : ∀ {n : ℕ} → Matrix 𝔹 (ℕ.suc n) (ℕ.suc n) → Fin (ℕ.suc n) → Fin (ℕ.suc n) → List ℕ
  bfs {n} g from to = let prev = bfs' g from to [ from ] [ from ] (constvec (ℕ.suc n) to)
                      in return-path prev to []
      where
      update-prevs : ∀ {n : ℕ}
        → Vec (Fin (ℕ.suc n)) (ℕ.suc n)
        → (Fin (ℕ.suc n))
        → List (Fin (ℕ.suc n))
        → Vec (Fin (ℕ.suc n)) (ℕ.suc n)
      update-prevs {n} ρ x [] = ρ
      update-prevs {n} ρ x (y ∷ ys) = let i = fromℕ< {toℕ x} {ℕ.suc n} (lemma3 (ℕ.suc n) x)
                                      in update-prevs (V.updateAt y (λ x → i) ρ) x ys
        
      bfs' : ∀ {n}
        → Matrix 𝔹 (ℕ.suc n) (ℕ.suc n)
        → (Fin (ℕ.suc n)) → (Fin (ℕ.suc n))
        → List (Fin (ℕ.suc n)) → List (Fin (ℕ.suc n))
        → Vec (Fin (ℕ.suc n)) (ℕ.suc n)
        → Vec (Fin (ℕ.suc n)) (ℕ.suc n)
      bfs' g from to Q σ ρ with Q
      ... | [] = ρ
      ... | x ∷ xs with filter-list (neighbors (row g x)) σ
      ... | [] = bfs' g from to xs σ ρ
      ... | y ∷ ys = bfs' g from to (xs ++ ys) (σ ++ ys) (update-prevs ρ x ys)

      return-path : ∀ {n : ℕ} → Vec (Fin (ℕ.suc n)) (ℕ.suc n) → Fin (ℕ.suc n) → List ℕ → List ℕ
      return-path prev indx res with (toℕ (V.lookup prev indx)) ≡? (toℕ to)
      ... | O = return-path prev (V.lookup prev indx) ((toℕ (V.lookup prev indx)) ∷ res)
      ... | I with (toℕ from) ≡? (toℕ to) | res
      ... | O | [] = res
      ... | O | xs = res ++ [ (toℕ to) ]
      ... | I | _ = res ++ [ (toℕ to) ]
