-- BFS algorithm
module Bfs where
  open import UndirGraph
  open import Matrix
  import Data.Vec as V
  open V using (Vec; _[_]≔_; []; _∷_)
  open import Presence
  open import Data.Fin.Base using (Fin; zero; suc; fromℕ; toℕ; inject≤; fromℕ<)
  open import Data.List
  open import Data.Nat.Base using (ℕ; _<_; s≤s; z≤n; _≤_)
  open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

  lemma1 : ∀ (n : ℕ) → n < ℕ.suc n
  lemma1 ℕ.zero = s≤s z≤n
  lemma1 (ℕ.suc n) = s≤s (lemma1 n)

  lemma2 : ∀ (n : ℕ) → ∀ (i : Fin n) → (toℕ i) < ℕ.suc n
  lemma2 (ℕ.suc n) zero = s≤s z≤n
  lemma2 (ℕ.suc n) (suc i) = s≤s (lemma2 n i)

  lemma3 : ∀ (n : ℕ) → ∀ (i : Fin n) → toℕ i < n
  lemma3 (ℕ.suc n) zero = s≤s z≤n
  lemma3 (ℕ.suc n) (suc i) = s≤s (lemma3 n i)
  
  -- Neighbors : Given a vector rapresenting the adiacency list of a
  -- node returns the indexes of the neighbor nodes (nodes reachable
  -- in 1 hop)
  {-# TERMINATING #-}
  neighbors : ∀ {n : ℕ} → Vec 𝔹 (ℕ.suc n) → List (indx n)
  neighbors {n} v = neighbors' v (fromℕ n) []
    where
    reduce : ∀ {n : ℕ} → indx n → indx n
    reduce zero = zero
    reduce {n} (Fin.suc zero) = zero
    reduce {n} (Fin.suc m) = fromℕ< {toℕ m} {ℕ.suc n} (lemma2 n m)

    neighbors' : ∀ {n : ℕ} → Vec 𝔹 (ℕ.suc n) → indx n → List (indx n) → List (indx n)
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

  lookup-l : ∀ {n : ℕ} → indx n → List (indx n) → 𝔹
  lookup-l x [] = O
  lookup-l x (y ∷ ys) with (toℕ x) ≡? (toℕ y)
  ... | I = I
  ... | O = lookup-l x ys

  -- Note : Vectors are explicity non-empty: The size is always n + 1
  -- ∀ n ∈ ℕ.
  filter-list : ∀ {n : ℕ} → List (indx n) → List (indx n) → List (indx n)
  filter-list [] m = []
  filter-list (x ∷ xs) ys with lookup-l x ys
  ... | I = filter-list xs ys
  ... | O = x ∷ (filter-list xs ys)

  -- Given a graph (its adiacency matrix) and an index (number of
  -- value at max n), return a list that rapresents the next indexes
  -- to see
  {-# TERMINATING #-}
  bfs-traverse : ∀ {n : ℕ} → graph[ ℕ.suc n ] → indx n → List (indx n)
  bfs-traverse g f = bfs-traverse' g [ f ] [] [ f ]
    where
    -- Given a graph and a list of already visited node and a list of
    -- successors return the list of next nodes to traverse the graph
    bfs-traverse' : ∀ {n : ℕ}
      → graph[ ℕ.suc n ]
      → List (indx n)
      → List (indx n)
      → List (indx n)
      → List (indx n)
    bfs-traverse' G Q L σ with Q
    ... | [] = L
    ... | x ∷ xs with filter-list (neighbors (row G x)) σ
    ... | [] = bfs-traverse' G xs (L ++ [ x ]) σ
    ... | ys = bfs-traverse' G (xs ++ ys) (L ++ [ x ]) (σ ++ ys)

  constvec : {A : Set} → (n : ℕ) → (val : A) → Vec A n
  constvec ℕ.zero val = []
  constvec (ℕ.suc n) val = val ∷ (constvec n val)

  update-prevs : ∀ {n : ℕ}
    → List (indx n)
    → (indx n)
    → List (indx n)
    → List (indx n)
  update-prevs {n} ρ x []       = ρ
  update-prevs {n} ρ x (y ∷ ys) =
    update-prevs (ρ [ y ]≔ fromℕ< {toℕ x} {ℕ.suc n} (lemma3 (ℕ.suc n) x)) x ys

  {-# TERMINATING #-}
  bfs' : ∀ {n}
    → graph[ ℕ.suc n ]              -- Graph G (its adjacency matrix)
    → (indx n) → (indx n)           -- from, to : Starting and ending point
    → List (indx n) → List (indx n) -- Q: Processing queue, σ : Seen list
    → List (indx n)                 -- ρ : previous nodes list :
                                    --     default ⇒ target node
    → List (indx n)
    -- TODO
    -- La chiave è qui: ρ parte come vettore costante, questo perchè
    -- in un grafo da n nodi una path tra due nodi ha un bound
    -- dall'alto: Il numero di nodi stesso. Se ce ne mette di più è
    -- perchè si fa un ciclo, cosa che non vogliamo. Ha più senso
    -- costruire un'algebra delle path e dimostrare che bfs torna la
    -- path con lunghezza minore. 
  bfs' g from to Q σ ρ with Q
  ... | [] = ρ
  ... | x ∷ xs with filter-list (neighbors (row g x)) σ
  ... | [] = bfs' g from to xs σ ρ
  ... | y ∷ ys = bfs' g from to (xs ++ ys) (σ ++ ys) (update-prevs ρ x ys)

  {-# TERMINATING #-}
  return-path : ∀ {n : ℕ}
    → Vec (indx n) (ℕ.suc n)    -- bfs' result
    → indx n                    -- starting node
    → indx n                    -- current node
    → indx n                    -- ending node
    → List (indx n)             -- current path
    → List (indx n)
  return-path prev from node to res with (toℕ (V.lookup prev node)) ≡? (toℕ to)
  ... | O =
    return-path prev from (V.lookup prev node) to ((V.lookup prev node) ∷ res)
  ... | I with (toℕ from) ≡? (toℕ to) | res
  ... | O | [] = res
  ... | O | xs = xs  ++ [ to ]
  ... | I | _  = res ++ [ to ]

  -- bfs itself: Given a graph, a starting index and a finish index,
  -- return the shortest path (a list of node indexes) between the
  -- starting point and the finish point
  {-# TERMINATING #-}
  bfs : ∀ {n : ℕ} → graph[ ℕ.suc n ] → indx n → indx n → List (indx n)
  bfs {n} g from to =
    return-path
    (bfs' g from to [ from ] [ from ] ([ to ]))
    from to to []
