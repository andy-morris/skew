{-# OPTIONS --rewriting #-}
module ExtNat where

open import Prelude
open Relation
open import Agda.Builtin.Equality.Rewrite

open import Bundles

private module ℕ-SR = Algebra.IsSemiring ℕ.*-+-isSemiring

open import Data.Nat.Tactic.RingSolver
open import Data.List using ([] ; _∷_)


private variable m n : ℕ


data ℕω : Set where
  [_] : (n : ℕ) → ℕω
  ω   : ℕω

private variable 𝐦 𝐧 : ℕω


private ⟦_⟧ : m ≡ n → [ m ] ≡ [ n ]
⟦_⟧ = ≡.cong [_]

plus : Op₂ ℕω
plus [ m ] [ n ] = [ m ℕ.+ n ]
plus [ _ ] ω     = ω
plus ω     n     = ω

mult : Op₂ ℕω
mult [ 0 ]         n         = [ 0 ]
mult [ m@(suc _) ] [ n ]     = [ m ℕ.* n ]
mult [   (suc _) ] ω         = ω
mult ω             [ 0 ]     = [ 0 ]
mult ω             [ suc _ ] = ω
mult ω             ω         = ω


data _≼_ : Rel ℕω lzero where
  refl : 𝐦 ≼ 𝐦
  []≼ω : [ m ] ≼ ω

private refl′ : ∀ {x y} → x ≡ y → x ≼ y
refl′ refl = refl


{-# REWRITE
    ℕ-SR.+-identityʳ
    ℕ-SR.*-identityʳ
    ℕ-SR.zeroʳ
    ℕ-SR.distribˡ
    ℕ-SR.distribʳ
    ℕ-SR.+-assoc
    ℕ-SR.*-assoc
  #-}

private
 module _ where
  open ≡.≡-Reasoning
  open Algebra.WithEq (≡-At ℕω)

  private [0] = [ 0 ]

  plus0ˡ : LeftIdentity [0] plus
  plus0ˡ [ n ] = refl
  plus0ˡ ω     = refl
  {-# REWRITE plus0ˡ #-}

  plus0ʳ : RightIdentity [0] plus
  plus0ʳ [ n ] = refl
  plus0ʳ ω     = refl
  {-# REWRITE plus0ʳ #-}

  mult0ʳ : RightZero [0] mult
  mult0ʳ [ zero  ] = refl
  mult0ʳ [ suc _ ] = refl
  mult0ʳ ω         = refl
  {-# REWRITE mult0ʳ #-}

  mult-[] : ∀ m n → mult [ m ] [ n ] ≡ [ m ℕ.* n ]
  mult-[] zero    zero    = refl
  mult-[] zero    (suc n) = refl
  mult-[] (suc m) zero    = refl
  mult-[] (suc m) (suc n) = refl
  {-# REWRITE mult-[] #-}

  mult-assoc : Associative mult
  mult-assoc [ zero ]  _         _         = refl
  mult-assoc [ suc _ ] [ zero ]  _         = refl
  mult-assoc [ suc _ ] [ suc _ ] [ _ ]     = refl
  mult-assoc [ suc _ ] [ suc _ ] ω         = refl
  mult-assoc [ suc _ ] ω         [ zero ]  = refl
  mult-assoc [ suc _ ] ω         [ suc _ ] = refl
  mult-assoc [ suc _ ] ω         ω         = refl
  mult-assoc ω         [ zero ]  _         = refl
  mult-assoc ω         [ suc _ ] [ zero ]  = refl
  mult-assoc ω         [ suc _ ] [ suc _ ] = refl
  mult-assoc ω         [ suc _ ] ω         = refl
  mult-assoc ω         ω         [ zero ]  = refl
  mult-assoc ω         ω         [ suc _ ] = refl
  mult-assoc ω         ω         ω         = refl
  {-# REWRITE mult-assoc #-}

  plus-mono : plus Preserves₂ _≼_ ⟶ _≼_ ⟶ _≼_
  plus-mono             refl refl = refl
  plus-mono             []≼ω []≼ω = []≼ω
  plus-mono {x = [ _ ]} refl []≼ω = []≼ω
  plus-mono {x = ω}     refl []≼ω = refl
  plus-mono {u = [ _ ]} []≼ω refl = []≼ω
  plus-mono {u = ω}     []≼ω refl = refl

  mult-mono : mult Preserves₂ _≼_ ⟶ _≼_ ⟶ _≼_
  mult-mono refl refl = refl
  mult-mono {[ zero ]} refl []≼ω = refl
  mult-mono {[ suc n ]} refl []≼ω = []≼ω
  mult-mono {ω} refl ([]≼ω {zero}) = []≼ω
  mult-mono {ω} refl ([]≼ω {suc m}) = refl
  mult-mono {u = [ zero ]} []≼ω refl = refl
  mult-mono {u = [ suc n ]} []≼ω refl = []≼ω
  mult-mono {u = ω} ([]≼ω {zero}) refl = []≼ω
  mult-mono {u = ω} ([]≼ω {suc m}) refl = refl
  mult-mono []≼ω []≼ω = []≼ω

  distribˡ : ∀ m n p → mult m (plus n p) ≡ plus (mult m n) (mult m p)
  distribˡ [ m ] [ n ] [ p ] = refl
  distribˡ [ zero ] [ n ] ω = refl
  distribˡ [ suc m ] [ n ] ω = refl
  distribˡ [ zero ] ω [ p ] = refl
  distribˡ [ suc m ] ω [ p ] = refl
  distribˡ [ zero ] ω ω = refl
  distribˡ [ suc m ] ω ω = refl
  distribˡ ω [ zero ] [ p ] = refl
  distribˡ ω [ suc n ] [ p ] = refl
  distribˡ ω [ zero ] ω = refl
  distribˡ ω [ suc n ] ω = refl
  distribˡ ω ω [ p ] = refl
  distribˡ ω ω ω = refl
  {-# REWRITE distribˡ #-}

  distribʳ : ∀ m n p → mult (plus m n) p ≡ plus (mult m p) (mult n p)
  distribʳ [ m ] [ n ] [ p ] = refl
  distribʳ [ zero ] [ n ] ω = refl
  distribʳ [ suc m ] [ n ] ω = refl
  distribʳ [ m ] ω [ zero ] = refl
  distribʳ [ m ] ω [ suc p ] = refl
  distribʳ [ zero ] ω ω = refl
  distribʳ [ suc m ] ω ω = refl
  distribʳ ω [ n ] [ zero ] = refl
  distribʳ ω [ n ] [ suc p ] = refl
  distribʳ ω [ n ] ω = refl
  distribʳ ω ω [ zero ] = refl
  distribʳ ω ω [ suc p ] = refl
  distribʳ ω ω ω = refl

instance natω-ssr : SSR ℕω _ _
natω-ssr = record
  { _≈_ = _≡_
  ; _⊴_ = _≼_
  ; _+_ = plus
  ; _*_ = mult
  ; 𝟎 = [ 0 ]
  ; 𝟏 = [ 1 ]
    ; isSSR = record
    { +-isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = ≡.isEquivalence
            ; ∙-cong = ≡.cong₂ plus
            }
          ; assoc = λ where
              [ m ] [ n ] [ p ] → ⟦ ℕ-SR.+-assoc m n p ⟧
              [ m ] [ n ] ω     → refl
              [ m ] ω     [ p ] → refl
              [ m ] ω     ω     → refl
              ω     [ n ] [ p ] → refl
              ω     [ n ] ω     → refl
              ω     ω     [ p ] → refl
              ω     ω     ω     → refl
          }
        ; identity =
            (λ{[ n ] → refl ; ω → refl}) ,
            (λ{[ n ] → ⟦ ℕ-SR.+-identityʳ n ⟧ ; ω → refl})
        }
      ; comm = λ where
          [ m ] [ n ] → ⟦ ℕ-SR.+-comm m n ⟧
          [ m ] ω     → refl
          ω     [ n ] → refl
          ω     ω     → refl
      }
    ; *-isSkewMonoid = record
      { ⊴-isPartialOrder = record
        { isPreorder = record
          { isEquivalence = ≡.isEquivalence
          ; reflexive = refl′
          ; trans = λ where
              refl refl → refl
              refl []≼ω → []≼ω
              []≼ω refl → []≼ω
          }
        ; antisym = λ{refl refl → refl}
        }
      ; isMagma = record
        { isEquivalence = ≡.isEquivalence
        ; ∙-cong = λ{≡.refl ≡.refl → ≡.refl}
        }
      ; 𝟏*-⊴ = λ where
          [ n ] → refl′ ⟦ ℕ-SR.+-identityʳ n ⟧
          ω     → refl
      ; ⊴-*𝟏 = λ where
          [ 0 ]     → refl
          [ suc n ] →
            refl′ ⟦ ≡.cong suc $ ≡.sym $ ℕ-SR.*-identityʳ n ⟧
          ω         → refl
      ; *-⊴-* = λ m n p → refl′ $ ≡.sym $ mult-assoc m n p
      ; *-mono = mult-mono
      }
    ; +-mono = plus-mono
    ; 𝟎*-⊴ = λ _ → refl
    ; ⊴-*𝟎 = λ where
        [ zero ] → refl
        [ suc n ] → refl′ ⟦ ≡.sym $ ℕ-SR.zeroʳ n ⟧
        ω → refl
    ; distribˡ = λ m n p → refl′ $ distribˡ m n p
    ; distribʳ = λ m n p → refl′ $ distribʳ m n p
    }
  }
