--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : ω×V → ω×W
--------------------------------------------------
open import Model.BaseCategory
open import Model.Modality

module Applications.CombiningFeatures.Model.Modalities.Lift {V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
-- open import Model.Type.Function
open import Model.LiftingModalities {ω} {V} {W} μ

ω×V : BaseCategory
ω×V = ω ⊗ V

ω×W : BaseCategory
ω×W = ω ⊗ W

open BaseCategory
open Ctx

private
  variable
    -- n : Ob ω
    -- n m n c₃ : Ob V
    -- w₁ w₂ : Ob W
    Γ Δ Θ : Ctx ω×W


--------------------------------------------------
-- ⟨ μ̃ ∣_⟩
{-
  Γ @ ω×W
  lift-ctx Γ ⊢ T type @ ω×V
  -----------------------------------------
  lift-ctx Γ ⟨ n ⟩ˡ ⊢ T ᵗʸ⟨ n ⟩ˡ type @ V
  Γ ⟨ n ⟩ˡ ,lock⟨ μ ⟩ ⊢ T ᵗʸ⟨ n ⟩ˡ [ to lift-ctx-naturalˡ ] type @ V
  ----------------------------------------------------------------------
  Γ ⟨ n ⟩ˡ ⊢ ⟨ μ | T ᵗʸ⟨ n ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ type @ W
-}

module _ (T : Ty (lift-ctx Γ)) where
  lift-ty-obj : (nw : Ob ω×W) → (γ : Γ ⟨ nw ⟩) → Set
  lift-ty-obj [ n , w ] γ = ⟨ μ ∣ T ᵗʸ⟨ n ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ hom-id ω , g ] , _ ⟫_ 
  lift-ty-morˡ : {n : Ob ω} {w₁ w₂ : Ob W} → 
                 (g : Hom W w₁ w₂) →
                 {γ₂ : Γ ⟨ [ n , w₂ ] ⟩} {γ₁ : Γ ⟨ [ n , w₁ ] ⟩} → 
                 Γ ⟪ [ hom-id ω , g ] ⟫ γ₂ ≡ γ₁ → 
                 lift-ty-obj [ n , w₂ ] γ₂ → lift-ty-obj [ n , w₁ ] γ₁
  lift-ty-morˡ {n} {w₁} {w₂} g {γ₂} {γ₁} eγ t = ⟨ μ ∣ T ᵗʸ⟨ n ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ g , eγ ⟫ t

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ f , hom-id W ] , _ ⟫_
  lift-ty-morʳ : {m n : Ob ω} {w : Ob W} → 
                 (f : Hom ω m n) →
                 {γ₂ : Γ ⟨ [ n , w ] ⟩} → 
                 lift-ty-obj [ n , w ] γ₂ → lift-ty-obj [ m , w ] (Γ ⟪ [ f , hom-id W ] ⟫ γ₂)
  lift-ty-morʳ f t = func (step₄ (mor-to-↣ˡ T f)) t
  {- 
    ⟨ μ̃ ∣ T ⟩ ⟪ [ f , g ] , _ ⟫_ 

                                                           lift-ty T ⟪ [ f , hom-id W {w₂} , refl ⟫_
    lift-ty T ⟨ [ m , w₂ ] , Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ⟩ ←----------------------------------------- lift-ty T ⟨ [ n , w₂ ] , γ₂ ⟩
                  |                                                  
                  | lift-ty T ⟪ [ hom-id ω {m} , g ] , eγ-decompnˡ Γ eγ ⟫_
                  ↓ 
    lift-ty T ⟨ [ m , w­₁ ] , γ₁ ⟩
  -}
  lift-ty-mor : {m n : Ob ω} {w₁ w₂ : Ob W} →
                (f : Hom ω m n) (g : Hom W w₁ w₂) →
                {γ₂ : Γ ⟨ [ n , w₂ ] ⟩} {γ₁ : Γ ⟨ [ m , w₁ ] ⟩} → 
                Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁ → 
                lift-ty-obj [ n , w₂ ] γ₂ → lift-ty-obj [ m , w₁ ] γ₁
  lift-ty-mor f g eγ t = lift-ty-morˡ g (eγ-decompnˡ Γ eγ) (lift-ty-morʳ f t)
