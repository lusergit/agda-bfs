-- BFS algorithm
module BfsC where
  open import Presence
  open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)
  open import UndirGraph
  open import Matrix
  import Data.Vec as V
  open V using (Vec; _[_]≔_; []; _∷_)
  import Data.Vec.Functional as VF
  open VF using (toList)
  open import Data.Fin.Base using (Fin; zero; suc; fromℕ; toℕ; inject≤; fromℕ<)
  open import Data.List
  open import Data.Nat.Base using (ℕ; _<_; s≤s; z≤n; _≤_)
  open import Relation.Nullary
  open import Data.List.Relation.Unary.Any


  lemma1 : ∀ (n : ℕ) → n < ℕ.suc n
  lemma1 ℕ.zero = s≤s z≤n
  lemma1 (ℕ.suc n) = s≤s (lemma1 n)

  lemma2 : ∀ (n : ℕ) → ∀ (i : Fin n) → (toℕ i) < ℕ.suc n
  lemma2 (ℕ.suc n) zero = s≤s z≤n
  lemma2 (ℕ.suc n) (suc i) = s≤s (lemma2 n i)

  lemma3 : ∀ (n : ℕ) → ∀ (i : Fin n) → toℕ i < n
  lemma3 (ℕ.suc n) zero = s≤s z≤n
  lemma3 (ℕ.suc n) (suc i) = s≤s (lemma3 n i)

  lemman : ∀ {n : ℕ} → n ≤ ℕ.suc n
  lemman {ℕ.zero} = z≤n
  lemman {ℕ.suc n} = s≤s lemman
  
  -- Neightbors : Given a vector rapresenting the adiacency list of a
  -- node returns the indexes of the neighbor nodes (nodes reachable
  -- in 1 hop)
  {-# TERMINATING #-}
  neighbors : ∀ {n : ℕ} → Vec 𝔹 (ℕ.suc n) → List (indx n)
  neighbors {n} v = neighbors' v (fromℕ n) []
    where
    reduce-n : ∀ {n : ℕ} → indx n → indx n
    reduce-n zero = zero
    reduce-n {n} (Fin.suc zero) = zero
    reduce-n {n} (Fin.suc m) = fromℕ< {toℕ m} {ℕ.suc n} (lemma2 n m)

    neighbors' : ∀ {n : ℕ} → Vec 𝔹 (ℕ.suc n) → indx n → List (indx n) → List (indx n)
    neighbors' v Fin.zero l with (V.lookup v Fin.zero)
    ... | I = Fin.zero ∷ l
    ... | O = l
    neighbors' v x l with (V.lookup v x)
    ... | I = neighbors' v (reduce-n x) (x ∷ l)
    ... | O = neighbors' v (reduce-n x) l

  data SPath : {n : ℕ} → (g : graph[ ℕ.suc n ]) → (i j : indx n) → List (indx n) → Set where
    ↯ : ∀ {n : ℕ} → (g : graph[ ℕ.suc n ]) (i : indx n) → SPath g i i [ i ]
    
    i→k→j : ∀ {n : ℕ} {xs : List (indx n)}
      → {g : graph[ ℕ.suc n ]}
      → {i j k : indx n}
      → SPath g i j xs                   -- if we have a path from a node i to a node j
      → Any (k ≡_) (neighbors (row g j)) -- k is a neighbor of j
      → ¬ (Any (k ≡_) xs)                -- k is not already in the shortest path
      → SPath g i k (xs ++ [ k ])        -- the sortest path from i to k is the shortest path to j ++ k
  
  bfs : ∀ {n : ℕ} {xs : List (indx n)} → (g : graph[ ℕ.suc n ]) → (i j : indx n) → {!!}
  bfs g frm to = {!!}
