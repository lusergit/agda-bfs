module SumRelation where
  data _⊎_ (X Y : Set) : Set where
    left  : X → X ⊎ Y
    right : Y → X ⊎ Y
