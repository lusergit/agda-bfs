module Matrix where

  open import Data.Empty
  open import Data.Nat.Base using (ℕ)
  open import Data.Fin using (Fin; zero; suc)
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_; _≢_)
  open P.≡-Reasoning
  open import Relation.Binary

  open import Function using (_∘_)

  import Data.Vec as V
  open V using (Vec)
  import Data.Vec.Properties as VP
  import Data.Vec.Functional.Relation.Binary.Pointwise as VP

  infix 8 _[_,_]

  Matrix : ∀ {a} (A : Set a) → ℕ → ℕ → Set a
  Matrix A r c = Vec (Vec A c) r

  -- LOOKUP --
  row : ∀ {r c a} {A : Set a} →  Matrix A r c → Fin r → Vec A c
  row = V.lookup

  lookup : ∀ {r c a} {A : Set a} → Matrix A r c → Fin r → Fin c → A
  lookup m i j = V.lookup (row m i) j

  _[_,_] :  ∀ {r c a} {A : Set a} → Matrix A r c → Fin r → Fin c → A
  m [ i , j ] = lookup m i j

  -- CREATING AND MANIPULATING --
  tabulate : ∀ {r c a} {A : Set a} → (Fin r → Fin c → A) → Matrix A r c
  tabulate f = V.tabulate (λ r → V.tabulate (λ c → f r c))

  transpose : ∀ {r c a} {A : Set a} → Matrix A r c → Matrix A c r
  transpose m = tabulate λ c r → lookup m r c

  diagonal : ∀ {a m n} {A : Set a} → A → A → Fin m → Fin n → A
  diagonal 0# 1# zero zero = 1#
  diagonal 0# 1# zero (suc c) = 0#
  diagonal 0# 1# (suc r) zero = 0#
  diagonal 0# 1# (suc r) (suc c) = diagonal 0# 1# r c

  -- Tabulate is an inverse of (flip lookup) --
  lookup∘tabulate : ∀ {a n} {A : Set a} {f : Fin n → Fin n → A} r c → lookup (tabulate f) r c ≡ f r c
  lookup∘tabulate {f = f} r c = begin
    V.lookup (V.lookup (V.tabulate (V.tabulate ∘ f)) r) c ≡⟨ P.cong (λ x → V.lookup x c) (VP.lookup∘tabulate (V.tabulate ∘ f) r) ⟩
    V.lookup (V.tabulate (f r)) c ≡⟨ VP.lookup∘tabulate (f r) c ⟩
    f r c ∎

  -- Pointwise check to tell weather two matrices are the same
  Pointwise : ∀ {s t ℓ} {S : Set s} {T : Set t} (_∼_ : REL S T ℓ) {m n} → Matrix S m n → Matrix T m n → Set ℓ
  Pointwise _~_ A B = ∀ r c → (A [ r , c ]) ~ (B [ r , c ])


  -- TESTS --
  -- Diagonal creates a diagonal

  diagonal-diag : ∀ {a n} {A : Set a} {0# : A} {1# : A} → (i : Fin n) → diagonal 0# 1# i i ≡ 1#
  diagonal-diag zero    = P.refl
  diagonal-diag (suc i) = diagonal-diag i

  diagonal-nondiag : ∀ {a n} {A : Set a} {0# : A} {1# : A} (i j : Fin n) → i ≢ j → diagonal 0# 1# i j ≡ 0#
  diagonal-nondiag zero zero i≢j = ⊥-elim (i≢j P.refl)
  diagonal-nondiag zero (suc j) i≢j = P.refl
  diagonal-nondiag (suc i) zero i≢j = P.refl
  diagonal-nondiag (suc i) (suc j) si≢sj = diagonal-nondiag i j (≢-suc si≢sj)
    where
      ≢-suc : ∀ {n} {i j : Fin n} → suc i ≢ suc j → i ≢ j
      ≢-suc si≢sj i≡j = ⊥-elim (si≢sj (P.cong suc i≡j))
