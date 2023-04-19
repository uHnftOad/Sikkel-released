--------------------------------------------------
-- Types in contexts over product base categories
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.TypeProdBase {C D : BaseCategory} where

-- open import Data.Unit using (⊤; tt)
-- open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product renaming (_,_ to [_,_])

open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextProdBase

open BaseCategory

private
  C×D : BaseCategory
  C×D = C ⊗ D
  
  variable
    c c₁ c₂ c₃ : Ob C
    d d₁ d₂ d₃ : Ob D
    Γ Δ Θ : Ctx C×D


--------------------------------------------------
-- Restrict a type in a context over C×D to a type in a context over D
fix-tyˡ : Ty Γ → (c : Ob C) → Ty (Γ ⟨ c ⟩ˡ)
fix-tyˡ T c ⟨ d , γ ⟩ = T ⟨ [ c , d ] , γ ⟩
fix-tyˡ T c ⟪ g , eγ ⟫ t = T ⟪ [ hom-id C , g ] , eγ ⟫ t
ty-cong (fix-tyˡ T c) e-hom = ty-cong T (×-≡,≡→≡ [ refl , e-hom ])
ty-id (fix-tyˡ T c) = ty-id T
ty-comp (fix-tyˡ T c) = trans (ty-cong T (×-≡,≡→≡ [ sym (hom-idˡ C) , refl ])) (ty-comp T)

-- Restrict a type in a context over C×D to a type in a context over C
fix-tyʳ : Ty Γ → (d : Ob D) → Ty (Γ ⟨ d ⟩ʳ)
fix-tyʳ T d ⟨ c , γ ⟩ = T ⟨ [ c , d ] , γ ⟩
fix-tyʳ T d ⟪ f , eγ ⟫ t = T ⟪ [ f , hom-id D ] , eγ ⟫ t
ty-cong (fix-tyʳ T d) e-hom = ty-cong T (×-≡,≡→≡ [ e-hom , refl ])
ty-id (fix-tyʳ T d) = ty-id T
ty-comp (fix-tyʳ T d) = trans (ty-cong T (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ty-comp T)

-- Alternative syntax for fix-tyˡ and fix-tyʳ
-- `ˡ` and `ʳ` indicate the direction of the restriction
_ᵗʸ⟨_⟩ˡ : Ty Γ → (c : Ob C) → Ty (Γ ⟨ c ⟩ˡ)
T ᵗʸ⟨ c ⟩ˡ = fix-tyˡ T c

_ᵗʸ⟨_⟩ʳ : Ty Γ → (d : Ob D) → Ty (Γ ⟨ d ⟩ʳ)
T ᵗʸ⟨ d ⟩ʳ = fix-tyʳ T d

