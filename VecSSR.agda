{-# OPTIONS --rewriting #-}
module VecSSR where

open import Prelude
open import Agda.Builtin.Equality.Rewrite

open import Bundles

open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Extensional
  as Pointwise using (Pointwise ; ext)


private
 variable
  a e r : Level
  𝐑 : Set a
  n : ℕ

private
  lookup/zipWith : {_•_ : Op₂ 𝐑} (xs ys : Vec 𝐑 n) (i : Fin n) →
                   lookup (zipWith _•_ xs ys) i ≡ lookup xs i • lookup ys i
  lookup/zipWith (x ∷ xs) (y ∷ ys) zero    = refl
  lookup/zipWith (x ∷ xs) (y ∷ ys) (suc i) = lookup/zipWith xs ys i
  {-# REWRITE lookup/zipWith #-}

  lookup/replicate : {x : 𝐑} (i : Fin n) → lookup (replicate x) i ≡ x
  lookup/replicate zero    = refl
  lookup/replicate (suc i) = lookup/replicate i
  {-# REWRITE lookup/replicate #-}

instance vec-ssr : ⦃ SSR 𝐑 e r ⦄ → SSR (Vec 𝐑 n) _ _
vec-ssr {𝐑 = 𝐑} ⦃ ssr ⦄ =
  record
    { _≈_ = Pointwise ssr._≈_
    ; _⊴_ = Pointwise ssr._⊴_
    ; _+_ = zipWith _+_
    ; _*_ = zipWith _*_
    ; 𝟎 = replicate 𝟎
    ; 𝟏 = replicate 𝟏
    ; isSSR = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = equiv
              ; ∙-cong = λ (ext xy) (ext uv) →
                  ext λ i → ssr.+-cong (xy i) (uv i)
              }
            ; assoc = λ x y z →
                ext λ i → ssr.+-assoc (lookup x i) (lookup y i) (lookup z i)
            }
          ; identity =
              (λ x → ext λ i → ssr.+-identityˡ (lookup x i)) ,
              (λ x → ext λ i → ssr.+-identityʳ (lookup x i))
          }
        ; comm = λ x y → ext λ i → ssr.+-comm (lookup x i) (lookup y i)
        }
      ; *-isSkewMonoid = record
        { ⊴-isPartialOrder = record
          { isPreorder = record
            { isEquivalence = equiv
            ; reflexive = λ (ext eq) → ext λ i → ssr.Le.reflexive (eq i)
            ; trans = λ (ext xy) (ext yz) →
                ext λ i → ssr.Le.trans (xy i) (yz i)
            }
          ; antisym = λ (ext xy) (ext yx) →
              ext λ i → ssr.Le.antisym (xy i) (yx i)
          }
        ; isMagma = record
          { isEquivalence = equiv
          ; ∙-cong = λ (ext xy) (ext uv) →
              ext λ i → ssr.*-cong (xy i) (uv i)
          }
        ; 𝟏*-⊴ = λ x → ext λ i → ssr.𝟏*-⊴ (lookup x i)
        ; ⊴-*𝟏 = λ x → ext λ i → ssr.⊴-*𝟏 (lookup x i)
        ; *-⊴-* = λ x y z → ext λ i →
            ssr.*-⊴-* (lookup x i) (lookup y i) (lookup z i)
        ; *-mono = λ (ext xy) (ext uv) →
            ext λ i → ssr.*-mono (xy i) (uv i)
        }
      ; +-mono = λ (ext xy) (ext uv) →
          ext λ i → ssr.+-mono (xy i) (uv i)
      ; 𝟎*-⊴ = λ x → ext λ i → ssr.𝟎*-⊴ (lookup x i)
      ; ⊴-*𝟎 = λ x → ext λ i → ssr.⊴-*𝟎 (lookup x i)
      ; distribˡ = λ x y z → ext λ i →
          ssr.distribˡ (lookup x i) (lookup y i) (lookup z i)
      ; distribʳ = λ x y z → ext λ i →
          ssr.distribʳ (lookup x i) (lookup y i) (lookup z i)
      }
    }
  where
    module ssr = SSR ssr
    equiv = Pointwise.isEquivalence ssr.Le.isEquivalence
