--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities.L-Term {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Function
open import Model.LiftingModalities.L-Context {C} {V} {W} μ
open import Model.LiftingModalities.L-Type {C} {V} {W} μ

open BaseCategory
open Ctx

private
  C×V : BaseCategory
  C×V = C ⊗ V

  C×W : BaseCategory
  C×W = C ⊗ W 

  variable
    Γ Δ Θ : Ctx C×W


--------------------------------------------------
-- mod-intro μ̃
module _ {T : Ty (lift-ctx Γ)} where
  {-
    lift-ctx Γ ⊢ t : T
    lift-ctx Γ ⟨ c ⟩ˡ ⊢ t ᵗᵐ⟨ c ⟩ˡ : T ᵗʸ⟨ c ⟩ˡ
    Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ t ᵗᵐ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]' : T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]
  -} 
  lift-tm : Tm (lift-ctx Γ) T → Tm Γ (lift-ty T)
  lift-tm t ⟨ [ c , w ] , γ ⟩' = mod-intro μ (t ᵗᵐ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]') ⟨ w , γ ⟩'
  Tm.naturality (lift-tm t) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {γ₂} {γ₁} [ f , g ] eγ = 
    begin
      lift-ty T ⟪ [ f , g ] , eγ ⟫ (lift-tm t ⟨ [ c₂ , w₂ ] , γ₂ ⟩')
    ≡⟨⟩
      lift-ty-morˡ T g (eγ-decompnˡ Γ eγ) (lift-ty-morʳ T f refl 
        (mod-intro μ (t ᵗᵐ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]') ⟨ w₂ , γ₂ ⟩'))
    ≡⟨ {!   !} ⟩ -- TODO: USE THE FACT THAT `t` ITSELF IS NATURAL
      mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ]') ⟨ w₁ , γ₁ ⟩' 
    ≡⟨⟩
      lift-tm t ⟨ [ c₁ , w₁ ] , γ₁ ⟩' ∎
    where open ≡-Reasoning