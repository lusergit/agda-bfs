-- Essentially the bool module, renaming true and false to symbolize
-- the presence or not of a path from a node to another
module Presence where
  data 𝔹 : Set where
    I O : 𝔹
