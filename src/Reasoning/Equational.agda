module Reasoning.Equational
  where
  open import Reasoning.Equality
  
  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _≡⟨⟩_
  infix  1 begin_

  _≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans p q

  _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
  x ≡⟨⟩ q = q

  _∎ : {A : Set} → (x : A) → x ≡ x
  x ∎ = refl

  begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin p = p

  cong : {A : Set} {x y : A} → (f : A → A) → x ≡ y → f x ≡ f y
  cong f refl = refl
  cong f (symm p) = symm (cong f p)
  cong f (trans p p₁) = trans (cong f p) (cong f p₁)

