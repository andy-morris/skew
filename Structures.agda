open import Prelude

module Structures {a e r} {A : Set a} (_≈_ : Rel A e) (_⊴_ : Rel A r) where

open Algebra.WithEq _≈_
open Relation
import Relation.Binary.Reasoning.PartialOrder as PO-Reasoning


private
  ℓ = a ⊔ e ⊔ r

  variable
    x y z 𝟎 𝟏 : A
    _*_ _+_ : Op₂ A


record IsSkewMonoid (_*_ : Op₂ A) (𝟏 : A) : Set ℓ where
  field
    ⊴-isPartialOrder : IsPartialOrder _≈_ _⊴_
    isMagma : IsMagma _*_

    𝟏*-⊴   : ∀ x → (𝟏 * x) ⊴ x
    ⊴-*𝟏   : ∀ x → x ⊴ (x * 𝟏)
    *-⊴-*  : ∀ x y z → ((x * y) * z) ⊴ (x * (y * z))
    *-mono : _*_ Preserves₂ _⊴_ ⟶ _⊴_ ⟶ _⊴_

  open module Le = IsPartialOrder ⊴-isPartialOrder public
    using (module Eq)
    renaming (isPreorder to ⊴-isPreorder ;
              ≤-respˡ-≈ to ⊴-respˡ-≈ ;
              ≤-respʳ-≈ to ⊴-respʳ-≈ ;
              ≤-resp-≈  to ⊴-resp-≈)

  open IsMagma isMagma public using (setoid)
    renaming (∙-cong to *-cong ; ∙-congˡ to *-congˡ ; ∙-congʳ to *-congʳ)

  poset : Poset _ _ _
  poset = record { isPartialOrder = ⊴-isPartialOrder }


record IsSkewSemiring (_+_ _*_ : Op₂ A) (𝟎 𝟏 : A) : Set ℓ where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid _+_ 𝟎
    *-isSkewMonoid : IsSkewMonoid _*_ 𝟏
    +-mono : _+_ Preserves₂ _⊴_ ⟶ _⊴_ ⟶ _⊴_

    𝟎*-⊴ : ∀ z → (𝟎 * z) ⊴ 𝟎
    ⊴-*𝟎 : ∀ x → 𝟎 ⊴ (x * 𝟎)

    distribˡ : ∀ x y z → ((x * y) + (x * z)) ⊴ (x * (y + z))
    distribʳ : ∀ x y z → ((x + y) * z) ⊴ ((x * z) + (y * z))

  open IsCommutativeMonoid +-isCommutativeMonoid public
    using ()
    renaming (∙-cong to +-cong ; ∙-congˡ to +-congˡ ; ∙-congʳ to +-congʳ ;
              identity to +-identity ; identityˡ to +-identityˡ ;
                identityʳ to +-identityʳ ;
              assoc to +-assoc ; comm to +-comm ;
              isMagma to +-isMagma ; isSemigroup to +-isSemigroup ;
              isCommutativeSemigroup to +-isCommutativeSemigroup ;
              isMonoid to +-isMonoid)

  open IsSkewMonoid *-isSkewMonoid public
    using (module Eq ; module Le ; poset ; setoid ; ⊴-isPartialOrder ;
           *-cong ; *-congˡ ; *-congʳ ;
           𝟏*-⊴ ; ⊴-*𝟏 ; *-⊴-* ; *-mono)
    renaming (isMagma to *-isMagma)



commSkew⇒commMon : IsSkewMonoid _*_ 𝟏 → Commutative _*_ →
                 IsCommutativeMonoid _*_ 𝟏
commSkew⇒commMon {_*_} {𝟏} sm comm = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = isMagma
      ; assoc = λ x y z → Le.antisym (*-⊴-* x y z) (assoc′ʳ x y z)
      }
    ; identity =
        (λ x → Le.antisym (𝟏*-⊴ x) (⊴-𝟏* x)) ,
        (λ x → Le.antisym (*𝟏-⊴ x) (⊴-*𝟏 x))
    }
  ; comm = comm
  }
 where
  open IsSkewMonoid sm
  open PO-Reasoning poset

  assoc′ʳ : ∀ x y z →  (x * (y * z)) ⊴ ((x * y) * z)
  assoc′ʳ x y z = begin
    (x * (y * z))   ≈⟨ comm x (y * z) ⟩
    ((y * z) * x)   ≤⟨ *-⊴-* y z x ⟩
    (y * (z * x))   ≈⟨ comm y (z * x) ⟩
    ((z * x) * y)   ≤⟨ *-⊴-* z x y ⟩
    (z * (x * y))   ≈⟨ comm z (x * y) ⟩
    ((x * y) * z)   ∎

  ⊴-𝟏* : ∀ x → x ⊴ (𝟏 * x)
  ⊴-𝟏* x = begin
    x         ≤⟨ ⊴-*𝟏 x ⟩
    (x * 𝟏)   ≈⟨ comm x 𝟏 ⟩
    (𝟏 * x)   ∎

  *𝟏-⊴ : ∀ x → (x * 𝟏) ⊴ x
  *𝟏-⊴ x = begin
    (x * 𝟏)   ≈⟨ comm x 𝟏 ⟩
    (𝟏 * x)   ≤⟨ 𝟏*-⊴ x ⟩
    x         ∎

commSkew⇒commSR : IsSkewSemiring _+_ _*_ 𝟎 𝟏 →
                 Commutative _*_ →
                 IsCommutativeSemiring _+_ _*_ 𝟎 𝟏
commSkew⇒commSR {_+_} {_*_} {𝟎} {𝟏} ss *-comm = record
  { isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isMonoid = isMonoid
      ; distrib =
          (λ x y z → Le.antisym (distribʳ′ x y z) (distribˡ  x y z)) ,
          (λ x y z → Le.antisym (distribʳ  y z x) (distribˡ′ x y z))
      }
    ; zero =
        (λ x → Le.antisym (𝟎*-⊴ x) (⊴-𝟎* x)) ,
        (λ x → Le.antisym (*𝟎-⊴ x) (⊴-*𝟎 x))
    }
  ; *-comm = *-comm
  }
 where
  open IsSkewSemiring ss
  open IsCommutativeMonoid (commSkew⇒commMon *-isSkewMonoid *-comm)
  open PO-Reasoning poset

  distribˡ′ : ∀ x y z → ((y * x) + (z * x)) ⊴ ((y + z) * x)
  distribˡ′ x y z = begin
    ((y * x) + (z * x))   ≈⟨ +-cong (*-comm y x) (*-comm z x) ⟩
    ((x * y) + (x * z))   ≤⟨ distribˡ x y z ⟩
    (x * (y + z))         ≈⟨ *-comm x (y + z) ⟩
    ((y + z) * x)         ∎

  distribʳ′ : ∀ x y z → (x * (y + z)) ⊴ ((x * y) + (x * z))
  distribʳ′ x y z = begin
    (x * (y + z))         ≈⟨ *-comm x (y + z) ⟩
    ((y + z) * x)         ≤⟨ distribʳ y z x ⟩
    ((y * x) + (z * x))   ≈⟨ +-cong (*-comm y x) (*-comm z x) ⟩
    ((x * y) + (x * z))   ∎

  ⊴-𝟎* : ∀ x → 𝟎 ⊴ (𝟎 * x)
  ⊴-𝟎* x = begin
    𝟎         ≤⟨ ⊴-*𝟎 x ⟩
    (x * 𝟎)   ≈⟨ *-comm x 𝟎 ⟩
    (𝟎 * x)   ∎

  *𝟎-⊴ : ∀ x → (x * 𝟎) ⊴ 𝟎
  *𝟎-⊴ x = begin
    (x * 𝟎)   ≈⟨ *-comm x 𝟎 ⟩
    (𝟎 * x)   ≤⟨ 𝟎*-⊴ x ⟩
    𝟎         ∎
