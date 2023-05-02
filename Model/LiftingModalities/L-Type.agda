--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities.L-Type {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Function
open import Model.LiftingModalities.L-Context {C} {V} {W} μ

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
-- Helper functions for defining `⟨ μ̃ ∣ _ ⟩`
module _ {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} where
  lock-fmap-naturalˡ : T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
  lock-fmap-naturalˡ = ≅ᵗʸ-trans (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (lift-ctx Γ ˢ⟪ f ⟫ˡ) (to lift-ctx-naturalˡ))
                                  (≅ᵗʸ-trans (ty-subst-cong-subst lift-ctx-cong-naturalˡ (T ᵗʸ⟨ c₁ ⟩ˡ))
                                  (≅ᵗʸ-sym (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (to lift-ctx-naturalˡ) (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)))))

  module _ (input : T ᵗʸ⟨ c₂ ⟩ˡ ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ˢ⟪ f ⟫ˡ ]) where
    step₁ : T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ]
    step₁ = ty-subst-map (to lift-ctx-naturalˡ) input
    
    step₂ : T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
    step₂ = from lock-fmap-naturalˡ ⊙ step₁

    step₃ : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] ⟩
    step₃ = mod-on-↣ μ step₂

    output : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ]
    output = to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ)) ⊙ step₃

{- TOO MUCH MEMORY; NOT USED
  output-cong : {T : Ty (lift-ctx Γ)} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} →
              {input₁ input₂ : T ᵗʸ⟨ c₂ ⟩ˡ ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ]} →
              input₁ ≅ⁿ input₂ →
              output input₁ ≅ⁿ output input₂
  output-cong {input₁ = input₁} {input₂ = input₂} s₁=s₂ = {!   !}

    where
      step₁-cong : step₁ input₁ ≅ⁿ step₁ input₂
      step₁-cong = ty-subst-map-cong s₁=s₂

      step₂-cong : step₂ input₁ ≅ⁿ step₂ input₂
      step₂-cong = ⊙-congˡ (from lock-fmap-naturalˡ) step₁-cong

      step₃-cong : step₃ input₁ ≅ⁿ step₃ input₂
      step₃-cong = mod-on-↣-cong μ step₂-cong

      proof : output input₁ ≅ⁿ output input₂
      proof = ? 
-}


--------------------------------------------------
-- ⟨ μ̃ ∣ _ ⟩

{-
  Γ @ C×W
  lift-ctx Γ ⊢ T type @ C×V
  -----------------------------------------
  lift-ctx Γ ⟨ c ⟩ˡ ⊢ T ᵗʸ⟨ c ⟩ˡ type @ V
  Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] type @ V
  ----------------------------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ ⟨ μ | T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ type @ W
-}

module _ {Γ : Ctx C×W} (T : Ty (lift-ctx Γ)) where
  lift-ty-obj : (cw : Ob C×W) → (γ : Γ ⟨ cw ⟩) → Set
  lift-ty-obj [ c , w ] γ = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ hom-id C , g ] , _ ⟫_ 
  lift-ty-mor-W : {c : Ob C} {w₁ w₂ : Ob W} → 
                  (g : Hom W w₁ w₂) →
                  {γ₂ : Γ ⟨ [ c , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c , w₁ ] ⟩} → 
                  (eγ : Γ ⟪ [ hom-id C , g ] ⟫ γ₂ ≡ γ₁) → 
                  lift-ty-obj [ c , w₂ ] γ₂ → lift-ty-obj [ c , w₁ ] γ₁
  lift-ty-mor-W {c} g eγ = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ g , eγ ⟫_

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ f , hom-id W ] , _ ⟫_
  lift-ty-mor-C : {c₁ c₂ : Ob C} {w : Ob W} → 
                  (f : Hom C c₁ c₂) →
                  {γ₂ : Γ ⟨ [ c₂ , w ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w ] ⟩} → 
                  (eγ : Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ≡ γ₁) → 
                  lift-ty-obj [ c₂ , w ] γ₂ → lift-ty-obj [ c₁ , w ] γ₁
  lift-ty-mor-C {c₁} f eγ t = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) eγ ⟫ (func (output (mor-to-↣ˡ T f)) t)

  lift-ty-mor-C-refl : {c₁ c₂ : Ob C} {w : Ob W} {f : Hom C c₁ c₂} {γ₂ : Γ ⟨ [ c₂ , w ] ⟩} {t : lift-ty-obj [ c₂ , w ] γ₂} →
                       lift-ty-mor-C f refl t ≡ func (output (mor-to-↣ˡ T f)) t
  lift-ty-mor-C-refl {c₁} = trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl) (ty-id ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) 
  
  {- 
    ⟨ μ̃ ∣ T ⟩ ⟪ [ f , g ] , _ ⟫_ 

                                                          lift-ty T ⟪ [ f , hom-id W {w₂} , refl ⟫_
    lift-ty T ⟨ [ c₁ , w₂ ] , Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ⟩ ←----------------------------------------- lift-ty T ⟨ [ c₂ , w₂ ] , γ₂ ⟩
                  |                                                  
                  | lift-ty T ⟪ [ hom-id C {c₁} , g ] , eγ-decompnˡ Γ eγ ⟫_
                  ↓ 
    lift-ty T ⟨ [ c₁ , w­₁ ] , γ₁ ⟩

                                                                                      lift-ty-mor-C f refl
    ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₂ , Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ⟩ ←------------------- ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₂ , γ₂ ⟩ ∋ t
                                      |                           
                                      | lift-ty-mor-W g (eγ-decompnˡ Γ eγ)
                                      ↓
    ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₁ , γ₁ ⟩ 
                    
  -}
  lift-ty-mor : {c₁ c₂ : Ob C} {w₁ w₂ : Ob W} →
                (f : Hom C c₁ c₂) (g : Hom W w₁ w₂) →
                {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} → 
                (eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁) → 
                lift-ty-obj [ c₂ , w₂ ] γ₂ → lift-ty-obj [ c₁ , w₁ ] γ₁
  lift-ty-mor f g eγ t = lift-ty-mor-W g (eγ-decompnˡ Γ eγ) (lift-ty-mor-C f refl t)
 

  --------------------------------------------------
  -- Proof of `ty-cong`
  {-
    S₁ = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ 
    S₂ = ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
    ψ₁ = lift-ty T ⟪ [ f₁ , hom-id W {w₂} , refl ⟫_
    ϕ₁ = lift-ty T ⟪ [ hom-id C {c₁} , g₁ ] , eγ-decompnˡ Γ eγ₁ ⟫_
    ψ₂ = lift-ty T ⟪ [ f₂ , hom-id W {w₂} , refl ⟫_
    ϕ₂ = lift-ty T ⟪ [ hom-id C {c₁} , g₂ ] , eγ-decompnˡ Γ eγ₂ ⟫_
    ▢ = ty-ctx-subst S₁ (eq (≅ˢ-cong-const-substˡ f₁=f₂) γ₂) 
      = T ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ) {w₂} {func (Γ ˢ⟪ f₁ ⟫ˡ) γ₂}) (eq (≅ˢ-cong-const-substˡ f₁=f₂) {w₂} γ₂) ⟫_

                                    ψ₁
    t ∈ S₂ ⟨ w₂ , γ₂ ⟩ -------------------------→ S₁ ⟨ w₂ , func (Γ ˢ⟪ f₁ ⟫ˡ) γ₂ ⟩
            |                                       ̷↗                   |
            |                                    ̷ ̷                      |       
            |                                 ̷ ̷                         | 
            |                              ̷ ̷                            |                                 
        ψ₂  |                        ▢  ̷ ̷ ▢⁻¹                           | ϕ₁
            |                        ̷ ̷                                  |
            |                     ̷ ̷                                     |
            |                  ̷ ̷                                        |
            |               ̷ ̷                                           |                                        
            ↓           ↙ ̷                                              ↓
          S₁ ⟨ w₂ , func (Γ ˢ⟪ f₂ ⟫ˡ) γ₂ ⟩ -------------------------→ S₁ ⟨ w₁ , γ₁ ⟩
                                                        ϕ₂
  -}
  lift-ty-mor-cong-W : {c : Ob C} {w₁ w₂ : Ob W} →
                       {g g' : Hom W w₁ w₂} (g=g' : g ≡ g') → 
                       {γ₂ γ₂' : Γ ⟨ [ c , w₂ ] ⟩} (γ₂=γ₂' : γ₂ ≡ γ₂') → 
                       {γ₁ : Γ ⟨ [ c , w₁ ] ⟩} → 
                       {eγ : Γ ⟪ [ hom-id C , g ] ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟪ [ hom-id C , g' ] ⟫ γ₂' ≡ γ₁} →
                       {t : lift-ty-obj [ c , w₂ ] γ₂} → 
                       lift-ty-mor-W g' eγ' (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ γ₂=γ₂' t) ≡ lift-ty-mor-W g eγ t
  lift-ty-mor-cong-W {c} refl refl = trans (sym (ty-comp ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩))
                                           (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (trans (hom-idˡ W) (sym refl)))

  lift-ty-mor-cong-C : {c₁ c₂ : Ob C} {w : Ob W} → 
                       {f f' : Hom C c₁ c₂} (f=f' : f ≡ f') → 
                       {γ₂ : Γ ⟨ [ c₂ , w ] ⟩} → 
                       {γ₁ γ₁' : Γ ⟨ [ c₁ , w ] ⟩} (γ₁=γ₁' : γ₁ ≡ γ₁') →
                       {eγ : Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟪ [ f' , hom-id W ] ⟫ γ₂ ≡ γ₁'} →
                       {t : lift-ty-obj [ c₂ , w ] γ₂} →
                       ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ γ₁=γ₁' (lift-ty-mor-C f eγ t) ≡ lift-ty-mor-C f' eγ' t
  lift-ty-mor-cong-C {c₁} {f = f} {f' = f'} refl refl {eγ = eγ} {eγ' = eγ'} {t} =
    begin 
      ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl (lift-ty-mor-C f eγ t)
    ≡⟨⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) refl ⟫ (lift-ty-mor-C f eγ t)
    ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ctx-id (Γ ⟨ c₁ ⟩ˡ) ⟫ (lift-ty-mor-C f eγ t)
    ≡⟨ ty-id ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟩
      lift-ty-mor-C f eγ t
    ≡⟨⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) eγ ⟫ _
    ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) eγ' ⟫ _
    ≡⟨⟩
      lift-ty-mor-C f' eγ' t ∎
    where open ≡-Reasoning

  lift-ty-cong : {c₁ c₂ : Ob C} {w₁ w₂ : Ob W} → 
                 {f f' : Hom C c₁ c₂} {g g' : Hom W w₁ w₂} → 
                 (e-hom : [ f , g ] ≡ [ f' , g' ]) → 
                 {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} → 
                 {eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟪ [ f' , g' ] ⟫ γ₂ ≡ γ₁} →
                 {t : lift-ty-obj [ c₂ , w₂ ] γ₂} →
                 lift-ty-mor f g eγ t ≡ lift-ty-mor f' g' eγ' t
  lift-ty-cong {c₁} {c₂} {w₁} {w₂} {f} {f'} {g} {g'} e-hom {γ₂} {γ₁} {eγ} {eγ'} {t} = proof
    where
      open ≡-Reasoning
      f=f' : f ≡ f'
      f=f' = proj₁ (,-injective e-hom)

      g=g' : g ≡ g'
      g=g' = proj₂ (,-injective e-hom)

      γ=γ' : Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ≡ Γ ⟪ [ f' , hom-id W ] ⟫ γ₂
      γ=γ' = cong (Γ ⟪_⟫ γ₂) (×-≡,≡→≡ [ f=f' , refl ])
      
      proof = 
        begin 
          lift-ty-mor f g eγ t
        ≡⟨⟩
          lift-ty-mor-W g (eγ-decompnˡ Γ eγ) (lift-ty-mor-C f refl t)
        ≡⟨ sym (lift-ty-mor-cong-W g=g' γ=γ' ) ⟩
          lift-ty-mor-W g' (eγ-decompnˡ Γ eγ') (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ γ=γ' (lift-ty-mor-C f refl t))
        ≡⟨ cong (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ')) (lift-ty-mor-cong-C f=f' γ=γ' ) ⟩
          lift-ty-mor-W g' (eγ-decompnˡ Γ eγ') (lift-ty-mor-C f' refl t)
        ≡⟨⟩
          lift-ty-mor f' g' eγ' t ∎ 


  --------------------------------------------------
  -- Proof of `ty-id`

  lift-ty-id : {c : Ob C} {w : Ob W} {γ : Γ ⟨ [ c , w ] ⟩} {t : lift-ty-obj [ c , w ] γ} → 
               lift-ty-mor (hom-id C) (hom-id W) (ctx-id Γ) t ≡ t
  lift-ty-id {c} {w} {γ} {t} = proof
    where
      open ≡-Reasoning
      eγ : Γ ⟪ [ hom-id C , hom-id W ] ⟫ (Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ) ≡ γ
      eγ = eγ-decompnˡ Γ (ctx-id Γ)

      r : Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ ≡ Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ
      r = refl

      helper₁ : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ hom-id C ⟫ˡ ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
      helper₁ = ≅ᵗʸ-trans (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)
      {- func (from helper₁) {w} {γ} t
        = func (from (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) 
               (func (from (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t)
        = func (from (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t
        = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (ctx-id Γ) t
        = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , eγ ⟫ t
      -}
      {- func (to helper₁) {w} {γ} t
        = func (to (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) 
               (func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t)
        = func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t
        = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (sym (ctx-id Γ)) t
        = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ? ⟫ t
        where ? : Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ ≡ Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ
                ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
                  ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ctx-id Γ ⟨ c ⟩ ⟫ t
                ≡ ⟨ ty-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟩
                  t
      -}

      helper₃ : func (output (mor-to-↣ˡ T (hom-id C))) t ≡ func (to helper₁) t
      helper₃ = 
        begin
          func (output (mor-to-↣ˡ T (hom-id C))) t
        ≡⟨⟩
          func (to (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ))) (func (mod-on-↣ μ (from lock-fmap-naturalˡ ⊙ (ty-subst-map (to lift-ctx-naturalˡ) (mor-to-↣ˡ T (hom-id C))))) t)
        ≡⟨ {!   !} ⟩
          ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c ⟩ˡ)) (sym (ctx-id (Γ ⟨ c ⟩ˡ))) ⟫ (⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ctx-id (Γ ⟨ c ⟩ˡ) ⟫ t)
        ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c ⟩ˡ)) (sym (ctx-id (Γ ⟨ c ⟩ˡ))) ⟫_) (ty-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) ⟩
          ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c ⟩ˡ)) (sym (ctx-id (Γ ⟨ c ⟩ˡ))) ⟫ t
        ≡⟨⟩
          func (to helper₁) t ∎

      proof : lift-ty-mor (hom-id C) (hom-id W) (ctx-id Γ) t ≡ t
      proof = 
        begin
          lift-ty-mor-W (hom-id W) eγ (lift-ty-mor-C (hom-id C) r t)
        ≡⟨ cong (lift-ty-mor-W (hom-id W) eγ) lift-ty-mor-C-refl ⟩
          ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , eγ ⟫ (func (output (mor-to-↣ˡ T (hom-id C))) t)
        ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
          ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (ctx-id (Γ ⟨ c ⟩ˡ)) _
        ≡⟨⟩
          func (from helper₁) {w} {γ} (func (output (mor-to-↣ˡ T (hom-id C))) t)
        ≡⟨ cong (func (from helper₁)) helper₃ ⟩
          func (from helper₁) (func (to helper₁) t)
        ≡⟨ eq (isoʳ helper₁) t ⟩
          t ∎

  --------------------------------------------------
  -- Proof of `ty-comp`

  -- NOT USED
  lift-ty-compˡ : {c : Ob C} {w₁ w₂ w₃ : Ob W} → 
                  {g : Hom W w₁ w₂} {g' : Hom W w₂ w₃} →
                  {γ₃ : Γ ⟨ [ c , w₃ ] ⟩} {γ₂ : Γ ⟨ [ c , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c , w₁ ] ⟩} →
                  {eγ-32 : Γ ⟪ [ hom-id C , g' ] ⟫ γ₃ ≡ γ₂} {eγ-21 : Γ ⟪ [ hom-id C , g ] ⟫ γ₂ ≡ γ₁} →
                  {t : lift-ty-obj [ c , w₃ ] γ₃} →
                  lift-ty-mor-W (_∙_ W g' g) (strong-ctx-comp (Γ ⟨ c ⟩ˡ) eγ-32 eγ-21) t ≡ lift-ty-mor-W g eγ-21 (lift-ty-mor-W g' eγ-32 t)
  lift-ty-compˡ {c} = ty-comp ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩

  lift-ty-comp : {c₁ c₂ c₃ : Ob C} {w₁ w₂ w₃ : Ob W} → 
                 {f : Hom C c₁ c₂} {f' : Hom C c₂ c₃} {g : Hom W w₁ w₂} {g' : Hom W w₂ w₃} →
                 {γ₃ : Γ ⟨ [ c₃ , w₃ ] ⟩} {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} →
                 {eγ-32 : Γ ⟪ [ f' , g' ] ⟫ γ₃ ≡ γ₂} {eγ-21 : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁} →
                 {t : lift-ty-obj [ c₃ , w₃ ] γ₃} →
                 lift-ty-mor (_∙_ C f' f) (_∙_ W g' g) (strong-ctx-comp Γ eγ-32 eγ-21) t ≡ lift-ty-mor f g eγ-21 (lift-ty-mor f' g' eγ-32 t)
  lift-ty-comp {c₁} {c₂} {c₃} {w₁} {w₂} {w₃} {f} {f'} {g} {g'} {γ₃} {γ₂} {γ₁} {eγ-32} {eγ-21} {t} = final
    where
      open ≡-Reasoning
      refl-c-21-w-22 : Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂ ≡ Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂
      refl-c-21-w-22 = refl

      refl-c-32-w-33 : Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃ ≡ Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃
      refl-c-32-w-33 = refl
      
      refl-c-31-w-33 : Γ ⟨ w₃ ⟩ʳ ⟪ _∙_ C f' f ⟫ γ₃ ≡ Γ ⟨ w₃ ⟩ʳ ⟪ _∙_ C f' f ⟫ γ₃
      refl-c-31-w-33 = refl

      refl-c-31-w-33-comp : Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃) ≡ Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)
      refl-c-31-w-33-comp = refl

      eγ-21' : Γ ⟨ c₁ ⟩ˡ ⟪ g ⟫ (Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂) ≡ γ₁
      eγ-21' = eγ-decompnˡ Γ eγ-21

      eγ-32' : Γ ⟨ c₂ ⟩ˡ ⟪ g' ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃) ≡ γ₂
      eγ-32' = eγ-decompnˡ Γ eγ-32

      eγ-comp : Γ ⟪ [ _∙_ C f' f , _∙_ W g' g ] ⟫ γ₃ ≡ γ₁
      eγ-comp = strong-ctx-comp Γ eγ-32 eγ-21

      eγ-comp' : Γ ⟨ c₁ ⟩ˡ ⟪ _∙_ W g' g ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ _∙_ C f' f ⟫ γ₃) ≡ γ₁
      eγ-comp' = eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)
      
      eγ-new : Γ ⟨ c₁ ⟩ˡ ⟪ g' ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)) ≡ Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂
      eγ-new = ty-subst-new-proof (Γ ˢ⟪ f ⟫ˡ) (eγ-decompnˡ Γ eγ-32)

      eγ-new' : Γ ⟨ c₁ ⟩ˡ ⟪ _∙_ W g' g ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)) ≡ γ₁ 
      eγ-new' = strong-ctx-comp (Γ ⟨ c₁ ⟩ˡ) eγ-new (eγ-decompnˡ Γ eγ-21)

      {-
        A = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
        B = ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
        
                                                            func (output (mor-to-↣ˡ T f))
        A [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₃ , Γ ⟪ [ f' , hom-id W ] ⟫ γ₃ ⟩ ←----------------------- B ⟨ w₃ , Γ ⟪ [ f' , hom-id W ] ⟫ γ₃ ⟩
                                    |                                                                         |
        A [ Γ ˢ⟪ f ⟫ˡ ] ⟪ g' , _ ⟫_ |                                                                         | B ⟪ g' , _ ⟫_
                                    ↓                                                                         ↓
                        A [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←-------------------------------------------------- B ⟨ w₂ , γ₂ ⟩
                                                              func (output (mor-to-↣ˡ T f))
      -}
      helper₁ : {s : lift-ty-obj [ c₂ , w₃ ] (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)} → 
                lift-ty-mor-W g' eγ-new (func (output (mor-to-↣ˡ T f)) s) ≡ func (output (mor-to-↣ˡ T f)) (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ-32) s)
      helper₁ = _↣_.naturality (output (mor-to-↣ˡ T f))

      helper₂ : lift-ty-mor-W g' eγ-new (lift-ty-mor-C f refl-c-31-w-33-comp (lift-ty-mor-C f' refl-c-32-w-33 t)) ≡ lift-ty-mor-C f refl-c-21-w-22 (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ-32) (lift-ty-mor-C f' refl-c-32-w-33 t))
      helper₂ = 
        begin
          lift-ty-mor-W g' eγ-new (lift-ty-mor-C f refl-c-31-w-33-comp (lift-ty-mor-C f' refl-c-32-w-33 t))
        ≡⟨ cong (lift-ty-mor-W g' eγ-new) lift-ty-mor-C-refl ⟩
          lift-ty-mor-W g' eγ-new (func (output (mor-to-↣ˡ T f)) (lift-ty-mor-C f' refl-c-32-w-33 t))
        ≡⟨ helper₁ ⟩
          func (output (mor-to-↣ˡ T f)) (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ-32) (lift-ty-mor-C f' refl-c-32-w-33 t))
        ≡˘⟨ lift-ty-mor-C-refl ⟩
          lift-ty-mor-C f refl-c-21-w-22 (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ-32) (lift-ty-mor-C f' refl-c-32-w-33 t)) ∎

      helper₃ : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ _∙_ C f' f ⟫ˡ ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] [ Γ ˢ⟪ f' ⟫ˡ ]
      helper₃ = ≅ᵗʸ-trans (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) 
                           (≅ᵗʸ-sym (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (Γ ˢ⟪ f ⟫ˡ) (Γ ˢ⟪ f' ⟫ˡ)))
      {- func (from helper₃) {w} {γ} t
        = func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (Γ ˢ⟪ f ⟫ˡ) (Γ ˢ⟪ f' ⟫ˡ))) 
               (func (from (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) {w} {γ} t)
        = func (from (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) {w} {γ} t
        = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (eq (⊚-comp-const-substˡ f f') γ) t
        = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w} , eγ ⟫ t
        where 
          eγ = trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ctx-comp Γ))
          eγ : Γ ⟨ c₁ ⟩ˡ ⟪ hom-id W ⟫ (Γ ⟨ w ⟩ʳ ⟪ _∙_ C f' f ⟫ γ) ≡ Γ ⟨ w ⟩ʳ ⟪ f ⟫ (Γ ⟨ w ⟩ʳ ⟪ f' ⟫ γ)
      -}
      {- func (to helper₃) {w} {γ} t
        = func (to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) {w} {γ} t
        = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (sym (eq (⊚-comp-const-substˡ f f') γ)) t
        = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w} , eγ ⟫ t
        where
          eγ = trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (sym (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ctx-comp Γ)))
          eγ : Γ ⟨ c₁ ⟩ˡ ⟪ hom-id W ⟫ (Γ ⟨ w ⟩ʳ ⟪ f ⟫ (Γ ⟨ w ⟩ʳ ⟪ f' ⟫ γ) ≡ Γ ⟨ w ⟩ʳ ⟪ _∙_ C f' f ⟫ γ
      -}

      helper₄ : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] [ Γ ˢ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩} →
                lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)) (func (to helper₃) {w₃} {γ₃} s) ≡ lift-ty-mor-W (_∙_ W g' g) eγ-new' s
      helper₄ {s} = 
        begin
          ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ _∙_ W g' g , eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21) ⟫ (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w₃} , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (sym (trans (cong (Γ ⟪_⟫ γ₃) (×-≡,≡→≡ [ refl , sym (hom-idˡ W) ])) (ctx-comp Γ))) ⟫ s)
        ≡˘⟨ ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟩
          ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ _∙_ W (hom-id W) (_∙_ W g' g) , strong-ctx-comp (Γ ⟨ c₁ ⟩ˡ) (trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (sym (trans (cong (Γ ⟪_⟫ γ₃) (×-≡,≡→≡ [ refl , sym (hom-idˡ W) ])) (ctx-comp Γ)))) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)) ⟫ s
        ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (hom-idˡ W) ⟩
          ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ _∙_ W g' g , eγ-new' ⟫ s ∎
        
      helper₅ : func (from helper₃) {w₃} {γ₃} (func (output (mor-to-↣ˡ T (_∙_ C f' f))) t) ≡ func (output (mor-to-↣ˡ T f)) (func (output (mor-to-↣ˡ T f')) t)
      helper₅ = 
        begin
          func (from helper₃) {w₃} {γ₃} (func (output (mor-to-↣ˡ T (_∙_ C f' f))) t)
        ≡⟨⟩
          ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w₃} , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (trans (cong (Γ ⟪_⟫ γ₃) (×-≡,≡→≡ [ refl , sym (hom-idˡ W) ])) (ctx-comp Γ)) ⟫
            (func (output (mor-to-↣ˡ T (_∙_ C f' f))) t)
        ≡⟨ ? ⟩
          func (output (mor-to-↣ˡ T f)) (func (output (mor-to-↣ˡ T f')) t) ∎
      -- func (output (mor-to-↣ˡ T f')) {w₃} {γ₃} : ⟨ μ ∣ T ᵗʸ⟨ c₃ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₃ , γ₃ ⟩ → ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩
      -- func (output (mor-to-↣ˡ T f)) : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩ → ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] [ Γ ˢ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩
      
      -- func (output (mor-to-↣ˡ T (_∙_ C f' f))) : ⟨ μ ∣ T ᵗʸ⟨ c₃ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₃ , γ₃ ⟩ → ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₃ , Γ ⟨ w ⟩ʳ ⟪ _∙_ C f' f ⟫ γ₃ ⟩
      -- ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w₃} , eγ ⟫_ : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₃ , Γ ⟨ w ⟩ʳ ⟪ _∙_ C f' f ⟫ γ₃ ⟩ → ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] [ Γ ˢ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩

      helper₉ : lift-ty-mor (_∙_ C f' f) (_∙_ W g' g) (strong-ctx-comp Γ eγ-32 eγ-21) t ≡ lift-ty-mor-W g (eγ-decompnˡ Γ eγ-21) (lift-ty-mor-W g' eγ-new (lift-ty-mor-C f refl (lift-ty-mor-C f' refl-c-32-w-33 t)))
      helper₉ = 
        begin
          lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)) (lift-ty-mor-C (_∙_ C f' f) refl t)
        ≡⟨ cong (lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21))) lift-ty-mor-C-refl ⟩
          lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)) 
            (func (output (mor-to-↣ˡ T (_∙_ C f' f))) t)
        ≡⟨⟩
          lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)) 
            (func (id-trans (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ _∙_ C f' f ⟫ˡ ])) _)
        ≡˘⟨ cong (lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21))) (eq (isoˡ helper₃) _) ⟩
          lift-ty-mor-W (_∙_ W g' g) (eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)) 
            (func (to helper₃) (func (from helper₃) _))
        ≡⟨ helper₄ ⟩
          lift-ty-mor-W (_∙_ W g' g) eγ-new' (func (from helper₃) _)
        ≡⟨ {!   !} ⟩
          lift-ty-mor-W (_∙_ W g' g) eγ-new' (func (output (mor-to-↣ˡ T f)) (func (output (mor-to-↣ˡ T f')) t))
        ≡˘⟨ cong (lift-ty-mor-W (_∙_ W g' g) eγ-new') lift-ty-mor-C-refl ⟩
          lift-ty-mor-W (_∙_ W g' g) eγ-new' (lift-ty-mor-C f refl-c-31-w-33-comp (func (output (mor-to-↣ˡ T f')) t))
       ≡˘⟨ cong (lift-ty-mor-W (_∙_ W g' g) eγ-new') (cong (lift-ty-mor-C f refl-c-31-w-33-comp) lift-ty-mor-C-refl) ⟩
          lift-ty-mor-W (_∙_ W g' g) eγ-new' (lift-ty-mor-C f refl-c-31-w-33-comp (lift-ty-mor-C f' refl-c-32-w-33 t))
        ≡⟨ ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟩
          lift-ty-mor-W g (eγ-decompnˡ Γ eγ-21) (lift-ty-mor-W g' eγ-new 
            (lift-ty-mor-C f refl-c-31-w-33-comp (lift-ty-mor-C f' refl-c-32-w-33 t))) ∎

      -- prop₄ : lift-ty-mor-W g (eγ-decompnˡ Γ eγ-21) (lift-ty-mor-W g' eγ-new (lift-ty-mor-C f refl (lift-ty-mor-C f' refl-c-32-w-33 t))) ≡ lift-ty-mor-W g (eγ-decompnˡ Γ eγ-21) (lift-ty-mor-C f refl-c-21-w-22 (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ-32) (lift-ty-mor-C f' refl-c-32-w-33 t)))
      -- prop₄ = {!   !} -- cong (lift-ty-mor-W g (eγ-decompnˡ Γ eγ-21)) helper₂

      final = {!   !} 

lift-ty : Ty (lift-ctx Γ) → Ty Γ
lift-ty T ⟨ [ c , w ] , γ ⟩ = lift-ty-obj T [ c , w ] γ
(lift-ty T) ⟪ [ f , g ] , eγ ⟫ t = lift-ty-mor T f g eγ t
ty-cong (lift-ty T) {f = [ f , g ]} {f' = [ f' , g' ]} e-hom = lift-ty-cong T {f = f} {f' = f'} {g = g} {g' = g'} e-hom
ty-id (lift-ty T) = {!!}
ty-comp (lift-ty T) = {!!}


--------------------------------------------------
-- Properties of ⟨ μ̃ ∣ _ ⟩
-- todo: UNCOMMENT FROM HERE
-- -- Proof of `Modality.mod-cong`
-- lift-ty-mod-cong : {T S : Ty (lift-ctx Γ)} → T ≅ᵗʸ S → lift-ty T ≅ᵗʸ lift-ty S
-- -- from : lift-ty T ↣ lift-ty S
-- func (from (lift-ty-mod-cong {Γ = Γ} {T} {S} T=S)) {[ c , w ]} {γ} = func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) {w} {γ}
-- {-
--     ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩ 
--   → ⟨ μ ∣ S ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩

--     ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c) 
--   : T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ≅ᵗʸ S ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]

--     mod-cong μ (ty-subst-cong-ty [ to lift-ctx-naturalˡ ] (ty-fix-ty-congˡ T=S c))
--   : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ≅ᵗʸ ⟨ μ ∣ S ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
-- -}
-- _↣_.naturality (from (lift-ty-mod-cong {Γ = Γ} {T} {S} T=S)) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {γ₁} {eγ} {t} = proof
--   where
--     open ≡-Reasoning
-- {-
--                                       lift-ty S ⟪ [ f , g ] , eγ ⟫_
--       lift-ty S ⟨ [ c₁ , w₁ ] , γ₁ ⟩ ←------------------------------ lift-ty S ⟨ [ c₂ , w₂ ] , γ₂ ⟩
--                                ↑                                        ↑
--   func from {[ c₁ , w₁ ]} {γ₁} |                                        | func from {[ c₂ , w₂ ]} {γ₂}
--                                |                                        |
--                                |                                        |
--       lift-ty T ⟨ [ c₁ , w₁ ] , γ₁ ⟩ ←------------------------ lift-ty T ⟨ [ c₂ , w₂ ] , γ₂ ⟩ ∋ t
--                                     lift-ty T ⟪ [ f , g ] , eγ ⟫_
-- -}
--     -- helper₁ : func (output (mor-to-↣ˡ S f)) (func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂)))) t) ≡ func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) (func (output (mor-to-↣ˡ T f)) t)
--     -- helper₁ = ? 
    
--     helper₂ : lift-ty-mor-C S f refl (func (from (lift-ty-mod-cong T=S)) t) ≡ func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) (lift-ty-mor-C T f refl t)
--     helper₂ = 
--       begin
--         lift-ty-mor-C S f refl (func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂)))) t)
--       ≡⟨ lift-ty-mor-C-refl S ⟩
--         func (output (mor-to-↣ˡ S f)) (func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂)))) t)
--       ≡⟨ {!   !} ⟩
--         func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) (func (output (mor-to-↣ˡ T f)) t)
--       ≡˘⟨ cong (func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁))))) (lift-ty-mor-C-refl T) ⟩
--         func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) (lift-ty-mor-C T f refl t) ∎

--     proof = 
--       begin
--         (lift-ty S) ⟪ [ f , g ] , eγ ⟫ (func (from (lift-ty-mod-cong T=S)) t)
--       ≡⟨⟩
--         lift-ty-mor-W S g (eγ-decompnˡ Γ eγ) (lift-ty-mor-C S f refl (func (from (lift-ty-mod-cong T=S)) t))
--       ≡⟨ cong (lift-ty-mor-W S g (eγ-decompnˡ Γ eγ)) helper₂ ⟩
--         lift-ty-mor-W S g (eγ-decompnˡ Γ eγ) (func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) _)
--       ≡⟨ _↣_.naturality (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) ⟩ 
--         func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁))))
--           (lift-ty-mor-W T g (eγ-decompnˡ Γ eγ) _)
--       ≡⟨⟩
--         func (from (lift-ty-mod-cong T=S)) ((lift-ty T) ⟪ [ f , g ] , eγ ⟫ t) ∎
-- func (to (lift-ty-mod-cong T=S)) {[ c , w ]} {γ} = func (to (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) {w} {γ}
-- _↣_.naturality (to (lift-ty-mod-cong T=S)) = {!   !}
-- -- isoˡ : to ⊙ from ≅ⁿ id-trans (lift-ty T)
-- eq (isoˡ (lift-ty-mod-cong T=S)) {[ c , w ]} t = eq (isoˡ (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) t
-- eq (isoʳ (lift-ty-mod-cong T=S)) {[ c , w ]} t = eq (isoʳ (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) t

-- -- Proof of `Modality.mod-natural`
-- fix-ty-lock-fmap-naturalˡ : (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Γ)} {c : Ob C} → 
--   (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ]
-- fix-ty-lock-fmap-naturalˡ σ {T} {c} = {!   !}

-- lift-ty-mod-natural : (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Γ)} →
--                       (lift-ty T) [ σ ] ≅ᵗʸ lift-ty (T [ lift-subst σ ])
-- -- from : (lift-ty T) [ σ ] ↣ lift-ty (T [ lift-subst σ ])
-- func (from (lift-ty-mod-natural σ)) {[ c , _ ]} = func (to (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ {c = c})) ⊙ from (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))
-- {-
--     ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ σ ˢ⟨ c ⟩ˡ ]
--   ↣ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩
--   = from (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) 

--     ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩ ⟨ w , γ ⟩
--   → ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩
--   = to (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))
-- -}
-- _↣_.naturality (from (lift-ty-mod-natural σ {T})) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {γ₁} {eγ} {t} = proof
--   where
--     open ≡-Reasoning
--     proof = {!   !}
-- -- to : lift-ty (T [ lift-subst σ ]) ↣ (lift-ty T) [ σ ]
-- func (to (lift-ty-mod-natural σ {T})) {[ c , _ ]} = func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) ⊙ from (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ)))
-- {-
--     ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
--   ↣ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩
--   = from (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))
--     ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩
--   ↣ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ σ ˢ⟨ c ⟩ˡ ]
--   = to (mod-natural μ (σ ˢ⟨ c ⟩ˡ))
-- -}
-- _↣_.naturality (to (lift-ty-mod-natural σ {T})) = {!   !}
-- -- isoˡ : to ⊙ from ≅ⁿ id-trans T
-- eq (isoˡ (lift-ty-mod-natural σ)) {[ c , _ ]} t = trans (cong (func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))) 
--                                                                   (eq (isoʳ (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))) (func (from (mod-natural μ (σ ˢ⟨ c ⟩ˡ))) t))) 
--                                                         (eq (isoˡ (mod-natural μ (σ ˢ⟨ c ⟩ˡ))) t)
-- -- isoʳ : from ⊙ to ≅ⁿ id-trans S
-- eq (isoʳ (lift-ty-mod-natural σ {T})) {[ c , w ]} t = trans (cong (func (to (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ)))) 
--                                                                   (eq (isoʳ (mod-natural μ (σ ˢ⟨ c ⟩ˡ))) (func (from (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))) t))) 
--                                                             (eq (isoˡ (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))) t)
