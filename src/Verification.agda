open import Presence
open import Data.List

module Verification where
  open import Bfs using (neighbors; bfs; return-path)
  open import UndirGraph
  open import Matrix

  open import Data.Nat.Base
  open import Data.List using (_∷_; [])
  open import Data.Vec.Base using (Vec; _∷_; [])
  open import Relation.Binary.PropositionalEquality.Core as EQ using (_≡_; _≢_; refl; cong)
  open import Data.Fin.Base using (Fin; zero; suc; fromℕ; toℕ; inject≤; fromℕ<)
  open import Relation.Nullary
  open import Data.List.Relation.Unary.Any

  -- ↯     : the shortest bath between a node and itself is the empty list
  -- i→j   : if I have the shortest path to a node, the shortest path to
  --         its immediate neighbors is going to that node
  -- i→k→j : If i can arrive to a node k, I can composethe shortest path
  --         for all the immediate sucessors of k that do not already appear
  --         in the shortes path
  data SPath : ∀ {n : ℕ} → graph[ ℕ.suc n ] → indx n → indx n → List (indx n) → Set where
    ↯     : ∀ {n : ℕ} {g : graph[ ℕ.suc n ]} {i j : indx n}
      → i ≡ j
      → SPath g i j [ i ]

    i→k→j : ∀ {n : ℕ}
      {g : graph[ ℕ.suc n ]} {i j k : indx n} {xs ys : List (indx n)}
      → SPath g i k xs
      → Any (j ≡_) (neighbors (row g k))
      → ¬ (Any (j ≡_) xs)
      → SPath g i j (xs ++ [ j ])

  return-path-base :
    (v : Vec (indx zero) (ℕ.suc zero)) →
    (i j k : indx zero) →
    (l : List (indx zero)) →
    (return-path v i j k l ≡ [ i ])
  return-path-base v zero zero zero xs = EQ.≡-Reasoning.begin
    return-path v zero zero zero xs EQ.≡-Reasoning.≡⟨ {!!} ⟩
    zero ∷ [] EQ.≡-Reasoning.∎

  return-path-induction : ∀ {n : ℕ} →
    (v : Vec (indx n) (ℕ.suc n)) →
    (i j k : indx n) →
    (l : List (indx n)) →
    (return-path v i j k l ≡ [ i ])
  return-path-induction = {!!}

  lemma-0 :
    (g : graph[ ℕ.suc ℕ.zero ]) →
    (i j : indx zero) →
    (bfs g i j) ≡ [ i ]
  lemma-0 g zero zero = {!!}

  lemma-1 :
    (g : graph[ ℕ.suc ℕ.zero ]) →
    (i j : indx zero) →
    SPath g i j [ i ]
  lemma-1 g zero zero = ↯ refl

  lemma-1a :
    (g : graph[ ℕ.suc ℕ.zero ]) →
    (i j : indx zero) →
    (bfs g i j) ≡ [ i ] →
    SPath g i j (bfs g i j) ≡ SPath g i j [ i ]
  lemma-1a g i j p = EQ.≡-Reasoning.begin
    SPath g i j (bfs g i j) EQ.≡-Reasoning.≡⟨ cong (λ x → SPath g i j x) p ⟩
    SPath g i j [ i ] EQ.≡-Reasoning.∎

  lemma-2 : ∀ {n : ℕ} {xs : List (indx n)}
    → (g : graph[ ℕ.suc n ])
    → (i k j : indx n)
    → SPath g i j xs
    → Any (j ≡_) (neighbors (row g k))
    → ¬ (Any (j ≡_) xs)
    → SPath g i j (xs ++ [ j ])
  lemma-2 g i k j path in-neighbors not-seen = {!!}

  theorem : ∀ {n : ℕ}
    → (g : graph[ ℕ.suc n ])
    → (i j : indx n)
    → SPath g i j (bfs g i j)
  theorem {zero} g i j = {!!}
  theorem {suc n} g i j = {!!}
