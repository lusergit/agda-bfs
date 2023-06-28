module Reasoning.Equality where
  data _≡_ {X : Set} : X → X → Set where
    refl : {a : X} → a ≡ a
    symm : {x y : X} → x ≡ y → y ≡ x
    trans : {x y z : X} → x ≡ y → y ≡ z → x ≡ z
