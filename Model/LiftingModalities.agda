--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Function

C×V : BaseCategory
C×V = C ⊗ V

C×W : BaseCategory
C×W = C ⊗ W

open BaseCategory
open Ctx

private
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

module _ {C D : BaseCategory} {Γ : Ctx (C ⊗ D)} {c₁ c₂ : Ob C} where
  
  eγ-decompn : {d₁ d₂ : Ob D} {f : Hom C c₁ c₂} {g : Hom D d₁ d₂} {γ₁ : Γ ⟨ [ c₁ , d₁ ] ⟩} {γ₂ : Γ ⟨ [ c₂ , d₂ ] ⟩} → 
    (eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁) → 
    Γ ⟪ [ hom-id C , g ] ⟫ (Γ ⟪ [ f , hom-id D ] ⟫ γ₂) ≡ γ₁
  eγ-decompn {f = f} {g = g} {γ₁ = γ₁} {γ₂ = γ₂} eγ = 
    begin 
      Γ ⟪ [ hom-id C , g ] ⟫ (Γ ⟪ [ f , hom-id D ] ⟫ γ₂)
    ≡˘⟨ ctx-comp Γ ⟩
      Γ ⟪ [ _∙_ C f (hom-id C) , _∙_ D (hom-id D) g ] ⟫ γ₂
    ≡⟨ cong (Γ ⟪_⟫ γ₂) (×-≡,≡→≡ [ hom-idʳ C , hom-idˡ D ]) ⟩
      Γ ⟪ [ f , g ] ⟫ γ₂ 
    ≡⟨ eγ ⟩ 
      γ₁ ∎
      where open ≡-Reasoning

  module _ (T : Ty Γ) where
    mor-to-term-tmˡ : (f : Hom C c₁ c₂) → (d : Ob D) → (γ : Γ ⟨ c₂ ⟩ˡ ⟨ d ⟩) → 
      ((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ])) ⟨ d , γ ⟩
    mor-to-term-tmˡ f d γd = MkFun fun natural 
      where
        fun : ∀ {b : Ob D} (ρ : Hom D b d) {γb : Γ ⟨ c₂ ⟩ˡ ⟨ b ⟩} (eγ : (Γ ⟨ c₂ ⟩ˡ) ⟪ ρ ⟫ γd ≡ γb) →
                T ᵗʸ⟨ c₂ ⟩ˡ ⟨ b , γb ⟩ → T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ] ⟨ b , γb ⟩
        fun {b} ρ eγ = T ⟪ [ f , hom-id D ] , refl ⟫_ 

        open ≡-Reasoning
        -- FIXME: fix the goals
        natural : ∀ {a b} {ρ-ab : Hom D a b} {ρ-bd : Hom D b d} {γa : Γ ⟨ c₂ ⟩ˡ ⟨ a ⟩} {γb : Γ ⟨ c₂ ⟩ˡ ⟨ b ⟩} →
                    {eγ-db : (Γ ⟨ c₂ ⟩ˡ) ⟪ ρ-bd ⟫ γd ≡ γb} {eγ-ba : (Γ ⟨ c₂ ⟩ˡ) ⟪ ρ-ab ⟫ γb ≡ γa} {t : T ᵗʸ⟨ c₂ ⟩ˡ ⟨ b , γb ⟩} →
                    fun {a} (_∙_ D ρ-bd ρ-ab) (strong-ctx-comp (Γ ⟨ c₂ ⟩ˡ) eγ-db eγ-ba) ((T ᵗʸ⟨ c₂ ⟩ˡ) ⟪ ρ-ab , eγ-ba ⟫ t) ≡ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ]) ⟪ ρ-ab , eγ-ba ⟫ (fun {b} ρ-bd eγ-db t)
        natural {a} {b} {ρ-ab} {ρ-bd} {γa} {γb} {eγ-db} {eγ-ba} {t} = 
            begin
              fun (_∙_ D ρ-bd ρ-ab) (strong-ctx-comp (Γ ⟨ c₂ ⟩ˡ) eγ-db eγ-ba) (T ᵗʸ⟨ c₂ ⟩ˡ ⟪ ρ-ab , eγ-ba ⟫ t)
            ≡⟨⟩
              T ⟪ [ f , hom-id D ] , refl ⟫ (T ᵗʸ⟨ c₂ ⟩ˡ ⟪ ρ-ab , eγ-ba ⟫ t)
            ≡⟨⟩
              T ⟪ [ f , hom-id D ] , refl ⟫ (T ⟪ [ hom-id C , ρ-ab ] , eγ-ba ⟫ t)
            ≡˘⟨ ty-comp T ⟩
              T ⟪ [ _∙_ C (hom-id C) f , _∙_ D ρ-ab (hom-id D) ] , _ ⟫ t
            ≡⟨ ty-cong T (×-≡,≡→≡ [ hom-idᵒ C , hom-idⁱ D ]) ⟩
              T ⟪ [ _∙_ C f (hom-id C) , _∙_ D (hom-id D) ρ-ab ] , _ ⟫ t
            ≡⟨ ty-comp T ⟩
              T ⟪ [ hom-id C , ρ-ab ] , _ ⟫ (T ⟪ [ f , hom-id D ] , refl ⟫ t)
            ≡⟨⟩
              (T ᵗʸ⟨ c₁ ⟩ˡ) ⟪ ρ-ab , _ ⟫ (T ⟪ [ f , hom-id D ] , refl ⟫ t)
            ≡⟨⟩
              (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ]) ⟪ ρ-ab , eγ-ba ⟫ (T ⟪ [ f , hom-id D ] , refl ⟫ t)
            ≡⟨⟩
              (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ]) ⟪ ρ-ab , eγ-ba ⟫ (fun ρ-bd eγ-db t) ∎
            where open ≡-Reasoning

    {-
      f : c₁ → c₂ @ C
      Γ ⊢ T type @ C×D
      ----------------------------------------------------------------
      Γ ⟨ c₂ ⟩ˡ ⊢ mor-to-termˡ T f : T ᵗʸ⟨ c₂ ⟩ˡ ⇛ T ᵗʸ⟨ c₁ ⟩ˡ @ D

      Transform a morphism in the left category into a term of function type in a context over the right category

      todo: define mor-to-termʳ and move these two somewhere else
    -}
    mor-to-termˡ : (f : Hom C c₁ c₂) → Tm (Γ ⟨ c₂ ⟩ˡ) ((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ]))
    mor-to-termˡ f = MkTm tm natural
      where
        tm = mor-to-term-tmˡ f
        natural : {b d : Ob D} {γd : Γ ⟨ c₂ ⟩ˡ ⟨ d ⟩} {γb : Γ ⟨ c₂ ⟩ˡ ⟨ b ⟩} → 
          (ρ-bd : Hom D b d) → (eγ-db : (Γ ⟨ c₂ ⟩ˡ) ⟪ ρ-bd ⟫ γd ≡ γb) → 
          ((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ])) ⟪ ρ-bd , eγ-db ⟫ (tm d γd) ≡ tm b γb
        natural {b = b} {d = d} {γd = γd} {γb = γb} ρ-bd eγ-db = to-pshfun-eq {γ = γb} {f = ((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ])) ⟪ ρ-bd , eγ-db ⟫ (tm d γd)} {g = tm b γb} pointwise-eq
          where 
            pointwise-eq : ∀ {a} (ρ-ab : Hom D a b) {γa} (eγ-ba : (Γ ⟨ c₂ ⟩ˡ) ⟪ ρ-ab ⟫ γb ≡ γa) t →
              (((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ])) ⟪ ρ-bd , eγ-db ⟫ (tm d γd)) $⟨ ρ-ab , eγ-ba ⟩ t ≡ (tm b γb) $⟨ ρ-ab , eγ-ba ⟩ t
            pointwise-eq _ _ _ = refl
              {-
                begin
                  (((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ])) ⟪ ρ-bd , eγ-db ⟫ (tm d γd)) $⟨ ρ-ab , eγ-ba ⟩ t
                ≡⟨⟩
                  (lower-presheaffunc ρ-bd eγ-db (tm d γd)) $⟨ ρ-ab , eγ-ba ⟩ t
                ≡⟨⟩
                  (tm d γd) $⟨ _∙_ D ρ-bd ρ-ab , strong-ctx-comp (Γ ⟨ c₂ ⟩ˡ) eγ-db eγ-ba ⟩ t
                ≡⟨⟩
                  T ⟪ [ f , hom-id D {a} ] , refl ⟫ t
                ≡⟨⟩ 
                  (tm b γb) $⟨ ρ-ab , eγ-ba ⟩ t ∎
              -}
    -- `_ᵗʸ⟨ _ ⟩ˡ` respects equivalence of subsitutions. 
    helper : {f₁ f₂ : Hom C c₁ c₂} → f₁ ≡ f₂ → 
           (T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f₁ ⟫ˡ ]) ≅ᵗʸ (T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f₂ ⟫ˡ ])
    helper f₁=f₂ = ⇛-cong ≅ᵗʸ-refl (ty-subst-cong-subst (≅ˢ-cong-const-substˡ f₁=f₂) (T ᵗʸ⟨ c₁ ⟩ˡ))
    
    {-
      Γ ⟨ c₂ ⟩ˡ ⊢ mor-to-termˡ T f₁ : (T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f₁ ⟫ˡ ])
      Γ ⟨ c₂ ⟩ˡ ⊢ mor-to-termˡ T f₂ : (T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f₂ ⟫ˡ ])
      --------------------------------------------------------------------------------------------------------
      Γ ⟨ c₂ ⟩ˡ ⊢ ι⁻¹[ helper T f₁=f₂ ] (mor-to-termˡ T f₁) : (T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f₂ ⟫ˡ ])
      QUESTION: 
        ?ψ : ι⁻¹[ helper T f₁=f₂ ] (mor-to-termˡ T f₁) ≅ᵗᵐ mor-to-termˡ T f₂
        ----------------------------------------------------------------------------
        tm-≅-to-≡ ψ : ι⁻¹[ helper T f₁=f₂ ] (mor-to-termˡ T f₁) ≡ mor-to-termˡ T f₂



      ψ : ι⁻¹[ helper T f₁=f₂ ] (mor-to-termˡ T f₁) ≅ᵗᵐ mor-to-termˡ T f₂
      eq ψ {w} γ : ι⁻¹[ helper T f₁=f₂ ] (mor-to-termˡ T f₁) ⟨ w , γ ⟩' ≡ mor-to-termˡ T f₂ ⟨ w , γ ⟩'
          ι⁻¹[ helper T f₁=f₂ ] (mor-to-termˡ T f₁) ⟨ w , γ ⟩'
        ≡⟨⟩
          ι[ ≅ᵗʸ-sym (helper T f₁=f₂) ] (mor-to-termˡ T f₁)
        ≡⟨⟩
          convert-term (from (helper T f₁=f₂)) (mor-to-termˡ T f₁) -- a PshFun object
        ≡⟨⟩
          to-pshfun-eq {b} {(T ᵗʸ⟨ c₂ ⟩ˡ)} {(T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f₂ ⟫ˡ ])} {γb}
                      {convert-term (from (helper T f₁=f₂)) (mor-to-termˡ T f₁)}
                      {mor-to-term-tmˡ T f₂ w γ} pointwise-eq
          where
            pointwise-eq : {a} (ρ-ab : Hom W a b) {γa} (eγ-ba : Γ ⟨ c₂ ⟩ˡ ⟪ ρ-ab ⟫ γ
        ≡⟨⟩
          MkFun fun₂ natural -- a PshFun object
        ≡⟨⟩
          mor-to-term-tmˡ T f₂ w γ
        ≡⟨⟩
          mor-to-termˡ T f₂ ⟨ w , γ ⟩'
    -}

module _ (T : Ty (lift-ctx Γ)) {c₁ c₂ : Ob C} (f : Hom C c₁ c₂) where

    -- Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩ ⊢ step₁ : ιc⁻¹[ lift-ctx-naturalˡ ] (T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ])
    step₁ : Tm (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) 
               (ιc⁻¹[ lift-ctx-naturalˡ ] ((T ᵗʸ⟨ c₂ ⟩ˡ) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ])))
    step₁ = ιc⁻¹[ lift-ctx-naturalˡ ]' (mor-to-termˡ T f)

    -- Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩ ⊢ step₂ : (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ])
    step₂ : Tm (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ((T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ]))
    step₂ = ι⁻¹[ ⇛-natural (to lift-ctx-naturalˡ) ] step₁

    -- Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩ ⊢ step₃ : (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ])
    step₃ : Tm (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) 
              ((T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]))
    step₃ = ι⁻¹[ ⇛-cong ≅ᵗʸ-refl S=S' ] step₂
      where
        S=S' : T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
        S=S' = ≅ᵗʸ-trans (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) ((lift-ctx Γ) ˢ⟪ f ⟫ˡ) (to lift-ctx-naturalˡ))
              (≅ᵗʸ-trans (ty-subst-cong-subst lift-ctx-cong-naturalˡ (T ᵗʸ⟨ c₁ ⟩ˡ))
                          (≅ᵗʸ-sym (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (to lift-ctx-naturalˡ) (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)))))
          {-
                T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ]
            ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ⊚ to lift-ctx-naturalˡ ]
            ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ⊚ (lift-ctx Γ) ˢ⟪ f ⟫ˡ ]
            ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
          -}

    -- (Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ])) ,lock⟨ μ ⟩ ⊢ step₄ : ((T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ])) [ lock-fmap μ π ]
    step₄ : Tm ((Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ])) ,lock⟨ μ ⟩) 
              (((T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ])) [ lock-fmap μ π ])
    step₄ = step₃ [ lock-fmap μ π ]' 

    -- (Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ])) ,lock⟨ μ ⟩ ⊢ step₅ : (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ π ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] [ lock-fmap μ π ])
    step₅ : Tm ((Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ])) ,lock⟨ μ ⟩) 
              ((T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ π ]) ⇛ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] [ lock-fmap μ π ]))
    step₅ = ι⁻¹[ ⇛-natural (lock-fmap μ π) ] step₄

    -- Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ]) ⊢ step₆ : ⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] [ lock-fmap μ π ])
    step₆ : Tm (Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ]))
              (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] [ lock-fmap μ π ]))
    step₆ = modality-map μ step₅ (ι⁻¹[ mod-natural μ π ] ξ)

    -- Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ]) ⊢ step₇ : (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]) [ π ]
    step₇ : Tm (Γ ⟨ c₂ ⟩ˡ ,, ⟨_∣_⟩ μ ((T ᵗʸ⟨ c₂ ⟩ˡ) [ to lift-ctx-naturalˡ ]))
              ((⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ])) [ π ])
    step₇ = ι[ mod-natural μ π ] step₆

    -- Γ ⟨ c₂ ⟩ˡ ⊢ step₈ : (⟨_∣_⟩ μ (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⇛ (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]))
    step₈ : Tm (Γ ⟨ c₂ ⟩ˡ)
              ((⟨_∣_⟩ μ (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⇛ (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ])))
    step₈ = lam (⟨_∣_⟩ μ (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ])) step₇

    step₉ : (w : Ob W) → (γ : Γ ⟨ c₂ ⟩ˡ ⟨ w ⟩) → 
      ⟨_∣_⟩ μ (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⟨ w , γ ⟩ →
      ⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]) ⟨ w , γ ⟩
    step₉ w γ = step₈ €⟨ w , γ ⟩_

    step₁₀ : (w : Ob W) → (γ : Γ ⟨ c₂ ⟩ˡ ⟨ w ⟩) → 
      ⟨_∣_⟩ μ (T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⟨ w , γ ⟩ →
      ⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ]) ⟨ w , Γ ⟪ [ f , hom-id W ] ⟫ γ ⟩
    step₁₀ w γ = (func (to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ))) {w} {γ}) ∘ (step₉ w γ)

{-
    mod-natural μ (Γ ˢ⟪ f₁ ⟫ˡ) : (⟨_∣_⟩ T) [ Γ ˢ⟪ f₁ ⟫ˡ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap Γ ˢ⟪ f₁ ⟫ˡ ])
    mod-natural μ (Γ ˢ⟪ f₂ ⟫ˡ) : (⟨_∣_⟩ T) [ Γ ˢ⟪ f₂ ⟫ˡ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap Γ ˢ⟪ f₂ ⟫ˡ ])
    ≅ˢ-cong-const-substˡ f₁=f₂ : Γ ˢ⟪ f₁ ⟫ˡ ≅ˢ Γ ˢ⟪ f₂ ⟫ˡ
    ty-subst-cong-subst (≅ˢ-cong-const-substˡ f₁=f₂) (⟨_∣_⟩ T) : (⟨_∣_⟩ T) [ Γ ˢ⟪ f₁ ⟫ˡ ] ≅ᵗʸ (⟨_∣_⟩ T) [ Γ ˢ⟪ f₂ ⟫ˡ ]

    to (mod-natural μ (Γ ˢ⟪ f₁ ⟫ˡ)) : ⟨_∣_⟩ (T [ lock-fmap Γ ˢ⟪ f₁ ⟫ˡ ]) ↣ (⟨_∣_⟩ T) [ Γ ˢ⟪ f₁ ⟫ˡ ]
    to (mod-natural μ (Γ ˢ⟪ f₂ ⟫ˡ)) : ⟨_∣_⟩ (T [ lock-fmap Γ ˢ⟪ f₂ ⟫ˡ ]) ↣ (⟨_∣_⟩ T) [ Γ ˢ⟪ f₂ ⟫ˡ ]
-}
--------------------------------------------------
-- μ̃ : Modality C×V C×W

{-
  Γ @ C×W
  lift-ctx Γ ⊢ T type @ C×V
  -----------------------------------------
  lift-ctx Γ ⟨ c ⟩ˡ ⊢ T ᵗʸ⟨ c ⟩ˡ type @ V
  Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ ιc⁻¹[ lift-ctx-naturalˡ ] (T ᵗʸ⟨ c ⟩ˡ) type @ V
  ----------------------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ ⟨ μ | T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ type @ W
-}
lift-ty : Ty (lift-ctx Γ) → Ty Γ
lift-ty T ⟨ [ c , w ] , γ ⟩ = ⟨ μ ∣ ιc⁻¹[ lift-ctx-naturalˡ ] (T ᵗʸ⟨ c ⟩ˡ) ⟩ ⟨ w , γ ⟩
_⟪_,_⟫_ (lift-ty {Γ = Γ} T) {[ c₁ , _ ]} {[ _ , w₂ ]} [ f , g ] {γ₂} {γ₁} eγ t = (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⟪ g , eγ-decompn {Γ = Γ} eγ ⟫ (step₁₀ T f w₂ γ₂ t)
ty-cong (lift-ty T) {[ f₁ , g₁ ]} {[ f₂ , g₂ ]} e-hom {γ₂} {γ₁} {eγ₁} {eγ₂} {t} = {!   !}
{-
    ty-cong (lift-ty T) {[ f₁ , g₁ ]} {[ f₂ , g₂ ]} e-hom {γ₂} {γ₁} {eγ₁} {eγ₂} {t}
  : (lift-ty T) ⟪ [ f₁ , g₁ ] , eγ₁ ⟫ t ≡ (lift-ty T) ⟪ [ f₂ , g₂ ] , eγ₂ ⟫ t
    f₁ f₂ : c₁ → c₂
    g₁ g₂ : w₁ → w₂

    e-homˡ : f₁ ≡ f₂ 
    e-homˡ = proj₁ (,-injective e-hom)

    e-homʳ : g₁ ≡ g₂
    e-homʳ = proj₂ (,-injective e-hom)
-}
  -- begin 
  --   (lift-ty T) ⟪ [ f₂ , g₂ ] , eγ₂ ⟫ t
  -- ≡⟨⟩
  --   (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⟪ g₁ , eγ-decompn {Γ = Γ} eγ₁ ⟫ (step₁₀ T f₁ w₂ γ₂ t)
  -- ≡⟨ ty-cong (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁₁ ⟩ˡ [ to lift-ctx-naturalˡ ])) (proj₂ (,-injective e-hom)) ⟩
  --   (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⟪ g₂ , eγ-decompn {Γ = Γ} eγ₂ ⟫ (step₁₀ T f₁ w₂ γ₂ t)
  -- ≡⟨ cong ((⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⟪ g₂ , eγ-decompn {Γ = Γ} eγ₂ ⟫_) proof ⟩
  --   (⟨_∣_⟩ μ (T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ])) ⟪ g₂ , eγ-decompn {Γ = Γ} eγ₂ ⟫ (step₁₀ T f₂ w₂ γ₂ t)
  -- ≡⟨⟩
  --   (lift-ty T) ⟪ [ f₂ , g₂ ] , eγ₂ ⟫ t 
  -- where
  -- proof : step₁₀ T f₁ w₂ γ₂ t ≡ step₁₀ T f₂ w₂ γ₂ t
ty-id (lift-ty T) = {!   !}
ty-comp (lift-ty T) = {!   !}


--------------------------------------------------
{-
  mod-cong : {Γ : Ctx D} {T S : Ty (lock Γ)} →
              T ≅ᵗʸ S → ⟨_∣_⟩ T ≅ᵗʸ ⟨_∣_⟩ S
    -- The action of this modality on types respects equivalence of types.
  mod-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} →
                (⟨_∣_⟩ T) [ σ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap σ ])
    -- The action of this modality on types commutes with type substitutions

  mod-intro : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm (lock Γ) T → Tm Γ (⟨_∣_⟩ T)
    -- The action of this modality on terms
      -- μ : C → D    lock(Γ) ⊢ t : T
      -- ----------------------------- TM/MODAL-INTRO
      -- Γ ⊢ mod-intro(t) : ⟨μ ∣ T⟩
  mod-intro-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm (lock Γ) T} →
                    t ≅ᵗᵐ t' → mod-intro t ≅ᵗᵐ mod-intro t'
    -- The action of this modality on terms respects equivalence of terms.
      -- μ : C → D    lock(Γ) ⊢ t t' : T    t ≅ᵗᵐ t'
      -- -------------------------------------------------------------------------
      -- Γ ⊢ mod-intro(t) mod-intro(t) : ⟨μ ∣ T⟩    mod-intro t ≅ᵗᵐ mod-intro t'
  mod-intro-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
                      (mod-intro t) [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ lock-fmap σ ]')
    -- The action of this modality on terms commutes with term substitutions
  mod-intro-ι : {Γ : Ctx D} {T S : Ty (lock Γ)} (T=S : T ≅ᵗʸ S) (t : Tm (lock Γ) S) →
                ι[ mod-cong T=S ] mod-intro t ≅ᵗᵐ mod-intro (ι[ T=S ] t)
    -- The action of this modality on terms commutes with term constructors `mod-intro` and ι[_]_
      -- Γ ⊢ mod-cong T=S : ⟨_∣ T⟩ ≅ᵗʸ ⟨_∣ S⟩
      -- Γ ⊢ mod-intro t : ⟨_ ∣ T⟩
      -- Γ ⊢ ι[ mod-cong T=S ] mod-intro t : Tm Γ ⟨_∣ S⟩
      -- lock Γ ⊢ ι[ T=S ] t : Tm (lock Γ) S
      -- Γ ⊢ mod-intro (ι[ T=S ] t) : Tm Γ ⟨_∣ S⟩

  mod-elim : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm Γ (⟨_∣_⟩ T) → Tm (lock Γ) T
    -- An elimination rule for terms
      -- Γ ⊢ t : ⟨_∣ T⟩
      -- --------------
      -- lock Γ ⊢ mod-elim t : T
  mod-elim-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm Γ (⟨_∣_⟩ T)} →
                  t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
  -- Naturality of mod-elim and the fact that it commutes with ι can be proved
  -- from mod-intro-natural, mod-intro-ι  and the β and η laws (see below).
  -- The elimination rule for terms respects equivalence of terms.

  mod-β : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
          mod-elim (mod-intro t) ≅ᵗᵐ t
    -- A β-rule
    -- If `lock Γ ⊢ t : T`, then `mod-elim (mod-intro t)` and `t` should be literally the same. 
  mod-η : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
          mod-intro (mod-elim t) ≅ᵗᵐ t
-}
  