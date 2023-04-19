--------------------------------------------------
-- Terms in contexts over product base categories
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.TermProdBase {C D : BaseCategory} where

-- open import Data.Unit using (⊤; tt)
-- open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product renaming (_,_ to [_,_])

open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextProdBase
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.TypeProdBase
open import Model.CwF-Structure.Term

open BaseCategory

private
  C×D : BaseCategory
  C×D = C ⊗ D
  
  variable
    c c₁ c₂ c₃ : Ob C
    d d₁ d₂ d₃ : Ob D
    Γ Δ Θ : Ctx C×D
    T S R A B : Ty Γ


--------------------------------------------------
-- Restrict a term in a context over C×D to a term in a context over D
fix-tmˡ : Tm Γ T → (c : Ob C) → Tm (Γ ⟨ c ⟩ˡ) (T ᵗʸ⟨ c ⟩ˡ)
fix-tmˡ t c ⟨ d , γ ⟩' = t ⟨ [ c , d ] , γ ⟩'
Tm.naturality (fix-tmˡ t c) g eγ = Tm.naturality t [ hom-id C , g ] eγ

-- Restrict a term in a context over C×D to a term in a context over C
fix-tmʳ : Tm Γ T → (d : Ob D) → Tm (Γ ⟨ d ⟩ʳ) (T ᵗʸ⟨ d ⟩ʳ)
fix-tmʳ t d ⟨ c , γ ⟩' = t ⟨ [ c , d ] , γ ⟩'
Tm.naturality (fix-tmʳ t d) f eγ = Tm.naturality t [ f , hom-id D ] eγ

-- Alternative syntax for fix-tmˡ and fix-tmʳ
-- `ˡ` and `ʳ` indicate the direction of the restriction
_ᵗᵐ⟨_⟩ˡ : Tm Γ T → (c : Ob C) → Tm (Γ ⟨ c ⟩ˡ) (T ᵗʸ⟨ c ⟩ˡ)
t ᵗᵐ⟨ c ⟩ˡ = fix-tmˡ t c

_ᵗᵐ⟨_⟩ʳ : Tm Γ T → (d : Ob D) → Tm (Γ ⟨ d ⟩ʳ) (T ᵗʸ⟨ d ⟩ʳ)
t ᵗᵐ⟨ d ⟩ʳ = fix-tmʳ t d

