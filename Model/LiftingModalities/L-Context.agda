--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities.L-Context {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Function

open BaseCategory
open Ctx

private
  C×V : BaseCategory
  C×V = C ⊗ V

  C×W : BaseCategory
  C×W = C ⊗ W 
  
  variable
    -- c c₁ c₂ c₃ : Ob C
    -- c c₁ c₂ c₃ : Ob V
    -- w₁ w₂ : Ob W
    Γ Δ Θ : Ctx C×W


--------------------------------------------------
-- The context operation of μ̃

lift-ctx : Ctx C×W → Ctx C×V
lift-ctx Γ ⟨ [ c , v ] ⟩ = Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v ⟩
ctx-hom (lift-ctx Γ) {[ c₁ , _ ]} {[ _ , v₂ ]} [ f , g ] γ = (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₂} γ)
ctx-id (lift-ctx Γ) {[ c , v ]} {γ} = 
  begin
    ctx-hom (lift-ctx Γ) {[ c , v ]} {[ c , v ]} [ hom-id C , hom-id V ] γ
  ≡⟨⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ hom-id V ⟫ (func (lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ)) {v} γ)
  ≡⟨ ctx-id (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟩
    func (lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ)) γ
  ≡⟨ eq (≅ˢ-trans (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (lock-fmap-id μ {Γ ⟨ c ⟩ˡ})) γ ⟩
    γ ∎
  where open ≡-Reasoning
  {-
    lock-fmap-cong μ (≅ˢ-id-const-substˡ Γ) : lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ) ≡ˢ lock-fmap μ (id-subst Γ ⟨ c ⟩ˡ)

    lock-fmap-id μ {Γ ⟨ c ⟩ˡ} : lock-fmap μ (id-subst Γ ⟨ c ⟩ˡ) ≡ˢ id-subst (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩)

    ≅ˢ-trans (lock-fmap-cong μ (≅ˢ-id-const-substˡ Γ)) (lock-fmap-id μ {Γ ⟨ c ⟩ˡ}) : lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ) ≡ˢ id-subst (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩)

    eq (≅ˢ-trans (lock-fmap-cong μ (≅ˢ-id-const-substˡ Γ)) (lock-fmap-id μ {Γ ⟨ c ⟩ˡ})) γ : func (lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ)) γ ≡ γ
  -}
ctx-comp (lift-ctx Γ) {[ c₁ , v₁ ]} {[ c₂ , v₂ ]} {[ c₃ , v₃ ]} {[ f₁ , g₁ ]} {[ f₂ , g₂ ]} {γ} = proof
  where
    open ≡-Reasoning
    helper : func (lock-fmap μ (Γ ˢ⟪ (_∙_) C f₂ f₁ ⟫ˡ)) {v₃} γ ≡ func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) (func (lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)) γ)
    helper = eq (≅ˢ-trans (lock-fmap-cong μ (⊚-comp-const-substˡ f₁ f₂)) (lock-fmap-⊚ μ (Γ ˢ⟪ f₁ ⟫ˡ) (Γ ˢ⟪ f₂ ⟫ˡ))) γ

    proof : lift-ctx Γ ⟪ (_∙_) C×V [ f₂ , g₂ ] [ f₁ , g₁ ] ⟫ γ ≡ lift-ctx Γ ⟪ [ f₁ , g₁ ] ⟫ (lift-ctx Γ ⟪ [ f₂ , g₂ ] ⟫ γ)
    proof = 
      begin
        lift-ctx Γ ⟪ (_∙_) C×V [ f₂ , g₂ ] [ f₁ , g₁ ] ⟫ γ
      ≡⟨⟩
        lift-ctx Γ ⟪ [ (_∙_) C f₂ f₁ , (_∙_) V g₂ g₁ ] ⟫ γ
      ≡⟨⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ (_∙_) V g₂ g₁ ⟫ (func (lock-fmap μ (Γ ˢ⟪ (_∙_) C f₂ f₁ ⟫ˡ)) {v₃} γ)
      ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ (_∙_) V g₂ g₁ ⟫_) helper ⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ (_∙_) V g₂ g₁ ⟫ (func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) (func (lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)) γ))
      ≡⟨ ctx-comp (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₁ ⟫ 
          ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫ 
            (func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) (func (lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)) γ)))
      ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₁ ⟫_) (_⇒_.naturality (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ))) ⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₁ ⟫ 
          (func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) {v₂} 
            ((Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫ 
              (func (lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)) {v₃} γ)))
      ≡⟨⟩
        lift-ctx Γ ⟪ [ f₁ , g₁ ] ⟫ (lift-ctx Γ ⟪ [ f₂ , g₂ ] ⟫ γ) ∎
  {-
    RHS: 
      ctx-comp (lift-ctx Γ) {[ c₁ , v₁ ]} {[ c₂ , v₂ ]} {[ c₃ , v₃ ]} {[ f₁ , g₁ ]} {[ f₂ , g₂ ]} {γ : Γ ⟨ c₃ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₃ ⟩}
    : ctx-hom (lift-ctx Γ) ([ f₂ , g₂ ] ∙ [ f₁ , g₁ ]) γ ≡ ctx-hom (lift-ctx Γ) [ f₁ , g₁ ] (ctx-hom (lift-ctx Γ) [ f₂ , g₂ ] γ)

                f₁                    f₂
    c₁ ------------------ c₂ -----------------→ c₃
    v₁ ------------------ v₂ -----------------→ v₃
                g₁                    g₂


                                [ c₁ , v₁ ]                    [ c₂ , v₁ ]                   [ c₃ , v₁ ]
                                    ↑                                  
                                    |                             
                                    | func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) {v₂}                             
                                [ c₁ , v₂ ] ←----------------- [ c₂ , v₂ ]                   [ c₃ , v₂ ]
                                    ↑                              ↑
    (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫_ |                              | Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫_
                                    |                              | 
                                [ c₁ , v₃ ] ←----------------- [ c₂ , v₃ ] ←----------------- [ c₃ , v₃ ]
                                      func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) {v₃} 
  -}
  {-      
        ctx-map-cong (⊚-comp-const-substˡ {D = V} Γ f₁ f₂)
      : lock-fmap μ (Γ ˢ⟪ f₂ ∙ f₁ ⟫ˡ) ≅ˢ lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ ⊚ Γ ˢ⟪ f₂ ⟫ˡ)

        lock-fmap-⊚ μ (Γ ˢ⟪ f₁ ⟫ˡ) (Γ ˢ⟪ f₂ ⟫ˡ)
      : lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ ⊚ Γ ˢ⟪ f₂ ⟫ˡ) ≡ˢ lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ) ⊚ lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)

        ≅ˢ-trans (ctx-map-cong (⊚-comp-const-substˡ {D = V} Γ f₁ f₂)) (lock-fmap-⊚ μ (Γ ˢ⟪ f₁ ⟫ˡ) (Γ ˢ⟪ f₂ ⟫ˡ))
      : lock-fmap μ (Γ ˢ⟪ f₂ ∙ f₁ ⟫ˡ) ≅ˢ lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ) ⊚ lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)
        eq (≅ˢ-trans (ctx-map-cong (⊚-comp-const-substˡ {D = V} Γ f₁ f₂)) (lock-fmap-⊚ μ (Γ ˢ⟪ f₁ ⟫ˡ) (Γ ˢ⟪ f₂ ⟫ˡ))) γ
      : func (lock-fmap μ (Γ ˢ⟪ f₂ ∙ f₁ ⟫ˡ)) γ ≡ func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ) ⊚ lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)) γ
      = func (lock-fmap μ (Γ ˢ⟪ f₂ ∙ f₁ ⟫ˡ)) γ ≡ func (lock-fmap μ (Γ ˢ⟪ f₁ ⟫ˡ)) (func (lock-fmap μ (Γ ˢ⟪ f₂ ⟫ˡ)) γ)
  -}

{-
  σ : Δ ⇒ Γ @ C×W
  ---------------------------------------------
  lift-subst σ : lift-ctx Δ ⇒ lift-ctx Γ @ C×V

  First take a projection of the given substitution σ : Δ ⇒ Γ @ C×W 
  along with c to obtain a substitution @ W; then apply the action 
  of modality μ on this new subsitutiton to obtain a substitution @ V. 
-}

lift-subst : Δ ⇒ Γ → lift-ctx Δ ⇒ lift-ctx Γ
func (lift-subst σ) {[ c , v ]} = func (lock-fmap μ (σ ˢ⟨ c ⟩ˡ)) {v}
_⇒_.naturality (lift-subst {Δ} {Γ} σ) {x = [ c₁ , v₁ ]} {y = [ c₂ , v₂ ]} {f = [ f , g ]} {δ = γ} =
  {-
                                    [ f , g ]
                    [ c₁ , v₁ ] -----------------→ [ c₂ , v₂ ]

                                    lift-ctx Δ ⟪ [ f , g ] ⟫_
        lift-ctx Δ ⟨ [ c₁ , v₁ ] ⟩ ←------------------------- lift-ctx Δ ⟨ [ c₂ , v₂ ] ⟩ ∋ γ
                       ∣                                                  ∣
    func {[ c₁ , v₁ ]} ∣                                                  ∣ func {[ c₂ , v₂ ]}
                       ↓                                                  ↓
        lift-ctx Γ ⟨ [ c₁ , v₁ ] ⟩ ←------------------------- lift-ctx Γ ⟨ [ c₂ , v₂ ] ⟩
                                    lift-ctx Γ ⟪ [ f , g ] ⟫_

      lift-ctx Γ ⟪ [ f , g ] ⟫ (func (lift-subst σ) {[ c₂ , v₂ ]} γ) ≡ func (lift-subst σ) {[ c₁ , v₁ ]} (lift-ctx Δ ⟪ [ f , g ] ⟫ γ)


      (func (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) {v₂} : Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ → Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
      (func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₂} : Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ → Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_ : Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ → Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩

      func (lock-fmap μ (Δ ˢ⟪ f ⟫ˡ)) {v₂} : Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ → Δ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
      (Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_ : Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ → Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩
      func (lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ)) {v₁} : Δ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ → Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩
                                                                                    
                                                      Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------------ Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ ∋ γ
                                                     / |                                                            / |             
                                                   /   |                                                          / (func (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) {v₂}
                                                 ∟     |            (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_              ∟     |
                                    Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------------ Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
                                                |      ↓                                                       |      ↓
                                                |      Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------- | ---- Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩             
    (func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₁} |     /                                                        |     / 
                                                |   / func (lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ)) {v₁}                | (func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₂}
                                                ↓ ∟                                                            ↓ ∟
                                    Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------------ Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
                                                                  (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_
                                  (func (lock-fmap μ (Δ ˢ⟪ f ⟫ˡ)) {v₂}
  -}
  {-
    Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ ←------------------------------------------- Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩      
                |                                                                         |
                | (func (lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ)) {v₂}                              | (func (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) {v₂}
                ↓                                                                         ↓
    Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ ←------------------------------------------- Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
                                   (func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₂}

      func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₂} (func (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) {v₂} γ)
    ≡⟨⟩
      func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ⊚ lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) {v₂} γ
    ≡⟨ eq (sym (lock-fmap-⊚ μ (Γ ˢ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ))) {v₂} γ ⟩
      func (lock-fmap μ ((Γ ˢ⟪ f ⟫ˡ) ⊚ (σ ˢ⟨ c₂ ⟩ˡ))) γ

    eq (lock-fmap-cong μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ˢ⟪ f ⟫ˡ)) γ : func (lock-fmap μ ((σ ˢ⟨ c₁ ⟩ˡ) ⊚ (Δ ˢ⟪ f ⟫ˡ))) γ ≡ func (lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ)) {v₂} (func (lock-fmap μ (Δ ˢ⟪ f ⟫ˡ)) {v₂} γ)
  -}
  begin
      lift-ctx Γ ⟪ [ f , g ] ⟫ (func (lift-subst σ) {[ c₂ , v₂ ]} γ)
    ≡⟨⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
        (func (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) {v₂} 
          (func (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) {v₂} γ))
    ≡˘⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-⊚ μ (Γ ˢ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) {v₂} γ) ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
        (func (lock-fmap μ ((Γ ˢ⟪ f ⟫ˡ) ⊚ (σ ˢ⟨ c₂ ⟩ˡ))) γ)
    ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-cong μ fix-const-substˡ) γ) ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫  
        (func (lock-fmap μ ((σ ˢ⟨ c₁ ⟩ˡ) ⊚ (Δ ˢ⟪ f ⟫ˡ))) γ)
    ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ˢ⟪ f ⟫ˡ)) γ) ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
        (func (lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ)) {v₂} 
          (func (lock-fmap μ (Δ ˢ⟪ f ⟫ˡ)) {v₂} γ))
    ≡⟨ _⇒_.naturality ((lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ))) ⟩
      func (lock-fmap μ (σ ˢ⟨ c₁ ⟩ˡ)) {v₁} 
        ((Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
          (func (lock-fmap μ (Δ ˢ⟪ f ⟫ˡ)) {v₂} γ))
    ≡⟨⟩
      func (lift-subst σ) {[ c₁ , v₁ ]} (lift-ctx Δ ⟪ [ f , g ] ⟫ γ) ∎
    where open ≡-Reasoning

lift-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → lift-subst σ ≅ˢ lift-subst τ
eq (lift-subst-cong σ=τ) = eq (lock-fmap-cong μ (fix-substˡ-cong σ=τ))

-- The action of `lift-ctx` on substitutions preserves identity morphisms.
lift-subst-id : lift-subst (id-subst Γ) ≅ˢ id-subst (lift-ctx Γ)
eq lift-subst-id = eq (≅ˢ-trans (lock-fmap-cong μ fix-substˡ-id) (lock-fmap-id μ))

-- The action of `lift-ctx` on substitutions commutes with the composition operation of Psh(C×W).
lift-subst-⊚ : (τ : Γ ⇒ Θ) → (σ : Δ ⇒ Γ) →
  lift-subst (τ ⊚ σ) ≅ˢ lift-subst τ ⊚ lift-subst σ
eq (lift-subst-⊚ τ σ) = eq (≅ˢ-trans (lock-fmap-cong μ (fix-substˡ-⊚ τ σ)) 
        (lock-fmap-⊚ μ (τ ˢ⟨ _ ⟩ˡ) (σ ˢ⟨ _ ⟩ˡ)))

-- A proof that `lift-ctx : CtxOp C×W C×V` is a functor
instance
  lift-ctx-is-functor : IsCtxFunctor lift-ctx
  ctx-map {{lift-ctx-is-functor}} = lift-subst
  ctx-map-cong {{lift-ctx-is-functor}} = lift-subst-cong
  ctx-map-id {{lift-ctx-is-functor}} = lift-subst-id
  ctx-map-⊚ {{lift-ctx-is-functor}} = lift-subst-⊚


--------------------------------------------------
-- Lemmas for defining μ̃ : Modality C×V C×W

-- `_⟨ _ ⟩ˡ` commutes with locks `lift-ctx` and `_,lock⟨ μ ⟩`. 
lift-ctx-naturalˡ : {c : Ob C} → lift-ctx Γ ⟨ c ⟩ˡ ≅ᶜ Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩
-- from : lift-ctx Γ ⟨ c ⟩ˡ ⇒ Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩
func (from lift-ctx-naturalˡ) = id
  {- 
      lift-ctx Γ ⟨ c ⟩ˡ ⟨ v ⟩ → Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v ⟩
    = lift-ctx Γ ⟨ [ c , v ] ⟩ → Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v ⟩
    = Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v ⟩ → Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v ⟩
  -}
_⇒_.naturality (from (lift-ctx-naturalˡ {Γ = Γ} {c = c})) {f = g} = 
  {-
                        g
              v₁ -----------------→ c₂

    (2)                          lift-ctx Γ ⟨ c ⟩ˡ ⟪ g ⟫_
    lift-ctx Γ ⟨ c ⟩ˡ ⟨ x ⟩ ←-------------------------------- lift-ctx Γ ⟨ c ⟩ˡ ⟨ y ⟩ ∋ δ
              ∣                                                             ∣
          id ∣                                                             ∣ id
              ↓                                                             ↓
    Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ x ⟩ ←--------------------------- Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ y ⟩
                                Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟪ g ⟫_                            (1)
  -}
  begin
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (from lift-ctx-naturalˡ) _)
  ≡⟨⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ _
  ≡˘⟨ cong ((Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-id μ) _) ⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (lock-fmap μ (id-subst (Γ ⟨ c ⟩ˡ))) _)
  ≡˘⟨ cong ((Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-cong μ ≅ˢ-id-const-substˡ) _) ⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (lock-fmap μ (Γ ˢ⟪ hom-id C {c} ⟫ˡ))  _)
  ≡⟨⟩
    lift-ctx Γ ⟪ [ hom-id C {c} , g ] ⟫ _
  ≡⟨⟩
    (lift-ctx Γ ⟨ c ⟩ˡ) ⟪ g ⟫ _ ∎
  where open ≡-Reasoning
-- to : Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⇒ lift-ctx Γ ⟨ c ⟩ˡ
func (to lift-ctx-naturalˡ) = id
_⇒_.naturality (to (lift-ctx-naturalˡ {Γ = Γ} {c = c})) {f = g} = 
  {-
                        g
              v₁ -----------------→ v₂

    (2)                          Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟪ g ⟫_
    Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩ ←--------------------------- Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ ∋ δ
              ∣                                             ∣
           id ∣                                             ∣ id
              ↓                                             ↓
    lift-ctx Γ ⟨ c ⟩ˡ ⟨ v₁ ⟩ ←-------------------------------- lift-ctx Γ ⟨ c ⟩ˡ ⟨ v₂ ⟩
                                  lift-ctx Γ ⟨ c ⟩ˡ ⟪ g ⟫_                                (1)
  -}
  begin
    (lift-ctx Γ ⟨ c ⟩ˡ) ⟪ g ⟫ (func (to lift-ctx-naturalˡ) _)
  ≡⟨⟩
    (lift-ctx Γ ⟨ c ⟩ˡ) ⟪ g ⟫ _
  ≡⟨⟩
    lift-ctx Γ ⟪ [ hom-id C {c} , g ] ⟫ _
  ≡⟨⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (lock-fmap μ (Γ ˢ⟪ hom-id C {c} ⟫ˡ)) _)
  ≡⟨ cong ((Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-cong μ ≅ˢ-id-const-substˡ) _) ⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (lock-fmap μ (id-subst (Γ ⟨ c ⟩ˡ))) _)
  ≡⟨ cong ((Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-id μ) _) ⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ _ ∎
  where open ≡-Reasoning
-- isoˡ : to ⊚ from ≅ˢ id-subst (lift-ctx Γ ⟨ c ⟩ˡ)
eq (isoˡ lift-ctx-naturalˡ) γ = refl 
-- isoʳ : from ⊚ to ≅ˢ id-subst (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩)
eq (isoʳ lift-ctx-naturalˡ) γ = refl

-- `_ˢ⟪ _ ⟫ˡ` and `lift-ctx-naturalˡ` are natural.
lift-ctx-cong-naturalˡ : {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} → 
  (lift-ctx Γ) ˢ⟪ f ⟫ˡ ⊚ to lift-ctx-naturalˡ ≅ˢ to lift-ctx-naturalˡ ⊚ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)
eq (lift-ctx-cong-naturalˡ {Γ = Γ} {c₁ = c₁}) γ = ctx-id (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩)

-- `_ᵗʸ⟨_⟩ˡ` is natural w.r.t. `lift-subst`
-- lift-subst-naturalˡ : {c : Ob C} {f : Hom C c c} → 
--   (lift-subst Γ) ᵗʸ⟨ f ⟩ˡ ⊚ to lift-subst-naturalˡ ≅ˢ to lift-subst-naturalˡ ⊚ lock-fmap μ (Γ ᵗʸ⟨ f ⟩ˡ)