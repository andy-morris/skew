module _ where

open import Prelude

open import Structures
open import Bundles
open import VecSSR

open import Relation.Binary
import Relation.Binary.Reasoning.PartialOrder as PO-Reasoning

open import Data.Vec as Vec using (Vec ; [] ; _∷_) hiding (module Vec)


private
 variable
  a e r : Level
  A 𝐑 : Set a
  m m′ n n′ o : ℕ

Mat : Set a → ℕ → ℕ → Set _
Mat 𝐑 m n = Vec (Vec 𝐑 n) m


⟨_] : ⦃ SSR 𝐑 e r ⦄ → Fin n → Vec 𝐑 n
⟨ zero  ] = 𝟏 ∷ Vec.replicate 𝟎
⟨ suc i ] = 𝟎 ∷ ⟨ i ]

𝕀 : ⦃ SSR 𝐑 e r ⦄ → Mat 𝐑 n n
𝕀 = Vec.tabulate ⟨_]

∑ ∏ : ⦃ SSR 𝐑 e r ⦄ → Vec 𝐑 n → 𝐑
∑ = Vec.foldl _ _+_ 𝟎
∏ = Vec.foldl _ _*_ 𝟏

∑′ ∏′ : ⦃ SSR 𝐑 e r ⦄ → Mat 𝐑 m n → 𝐑
∑′ = ∑ ∘ Vec.map ∑
∏′ = ∏ ∘ Vec.map ∏

_⊗_ : ⦃ SSR 𝐑 e r ⦄ → Mat 𝐑 m n → Mat 𝐑 n o → Mat 𝐑 m o
𝑀 ⊗ 𝑁 = map (λ 𝑚 → map (λ 𝑛 → ∑ (𝑚 * 𝑛)) (transpose 𝑁)) 𝑀
  where open Vec

shuf : (Fin m → Fin m′) → (Fin n → Fin n′) → Mat 𝐑 m′ n′ → Mat 𝐑 m n
shuf f g 𝑀 = tabulate λ i → tabulate λ j → lookup (lookup 𝑀 (f i)) (g j)
  where open Vec
