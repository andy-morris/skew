module Bundles where

open import Prelude
open import Structures

record SSR {a} (𝐑 : Set a) e r : Set (a ⊔ lsuc e ⊔ lsuc r) where
  infix  1 _≈_ _⊴_ _≉_ _◅_ _▻_ _⊵_
  infixl 6 _+_
  infixl 7 _*_
  field
    _≈_ : Rel 𝐑 e
    _⊴_ : Rel 𝐑 r
    _+_ _*_ : Op₂ 𝐑
    𝟎 𝟏 : 𝐑
    isSSR : IsSkewSemiring _≈_ _⊴_ _+_ _*_ 𝟎 𝟏

  open IsSkewSemiring isSSR public

  _≉_ _◅_ _▻_ _⊵_ : Rel 𝐑 _
  x ≉ y = ¬ (x ≈ y)
  x ◅ y = (x ⊴ y) × (x ≉ y)
  _⊵_ = flip _⊴_
  _▻_ = flip _◅_

open SSR ⦃ … ⦄ public using (_≈_ ; _≉_ ; _⊴_ ; _◅_ ; _+_ ; _*_ ; 𝟎 ; 𝟏)
