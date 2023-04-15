--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
open import Model.BaseCategory
open import Model.Modality

module Applications.CombiningFeatures.Model.Modalities.Lift-general {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Nat
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
-- open import Data.Product renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injectiveʳ)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure

open BaseCategory
open Ctx

C×V : BaseCategory
C×V = C ⊗ V

C×W : BaseCategory
C×W = C ⊗ W

private
  variable
    -- c₁ c₂ : Ob C
    -- v₁ v₂ : Ob V
    -- w₁ w₂ : Ob W
    Γ Δ Θ : Ctx C×W


--------------------------------------------------
-- The context operation of μ̃
 
temp-ctx : Ctx C×W → Ctx C×V
temp-ctx Γ ⟨ [ c , v ] ⟩ = Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⟨ v ⟩
ctx-hom (temp-ctx Γ) {[ c₁ , _ ]} {[ _ , v₂ ]} [ f , g ] γ = (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ (func (lock-fmap μ (const-substˡ Γ f)) {v₂} γ)
ctx-id (temp-ctx Γ) {[ c , v ]} {γ} = 
  begin
    ctx-hom (temp-ctx Γ) {[ c , v ]} {[ c , v ]} [ hom-id C , hom-id V ] γ
  ≡⟨⟩
    (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟪ hom-id V ⟫ (func (lock-fmap μ (const-substˡ Γ (hom-id C))) {v} γ)
  ≡⟨ ctx-id (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩) ⟩
    func (lock-fmap μ (const-substˡ Γ (hom-id C))) γ
  ≡⟨ eq (≅ˢ-trans (lock-fmap-cong μ (≅ˢ-const-substˡ Γ)) (lock-fmap-id μ {Γ ⟨ c ⟩ˡ})) γ ⟩
    γ ∎
  where open ≡-Reasoning
  {-
    lock-fmap-cong μ (≅ˢ-const-substˡ Γ) : lock-fmap μ (const-substˡ Γ (hom-id C)) ≡ˢ lock-fmap μ (id-subst Γ ⟨ c ⟩ˡ)

    lock-fmap-id μ {Γ ⟨ c ⟩ˡ} : lock-fmap μ (id-subst Γ ⟨ c ⟩ˡ) ≡ˢ id-subst (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩)

    ≅ˢ-trans (lock-fmap-cong μ (≅ˢ-const-substˡ Γ)) (lock-fmap-id μ {Γ ⟨ c ⟩ˡ}) : lock-fmap μ (const-substˡ Γ (hom-id C)) ≡ˢ id-subst (Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩)

    eq (≅ˢ-trans (lock-fmap-cong μ (≅ˢ-const-substˡ Γ)) (lock-fmap-id μ {Γ ⟨ c ⟩ˡ})) γ : func (lock-fmap μ (const-substˡ Γ (hom-id C))) γ ≡ γ
  -}
ctx-comp (temp-ctx Γ) {[ c₁ , v₁ ]} {[ c₂ , v₂ ]} {[ c₃ , v₃ ]} {[ f₁ , g₁ ]} {[ f₂ , g₂ ]} {γ} = proof
  where
    open ≡-Reasoning
    helper : func (lock-fmap μ (const-substˡ Γ ((_∙_) C f₂ f₁))) {v₃} γ ≡ func (lock-fmap μ (const-substˡ Γ f₁)) (func (lock-fmap μ (const-substˡ Γ f₂)) γ)
    helper = eq (≅ˢ-trans (lock-fmap-cong μ (⊚-comp-const-substˡ {D = W} Γ f₁ f₂)) (lock-fmap-⊚ μ (const-substˡ Γ f₁) (const-substˡ Γ f₂))) γ

    proof : temp-ctx Γ ⟪ (_∙_) C×V [ f₂ , g₂ ] [ f₁ , g₁ ] ⟫ γ ≡ temp-ctx Γ ⟪ [ f₁ , g₁ ] ⟫ (temp-ctx Γ ⟪ [ f₂ , g₂ ] ⟫ γ)
    proof = 
      begin
        temp-ctx Γ ⟪ (_∙_) C×V [ f₂ , g₂ ] [ f₁ , g₁ ] ⟫ γ
      ≡⟨⟩
        temp-ctx Γ ⟪ [ (_∙_) C f₂ f₁ , (_∙_) V g₂ g₁ ] ⟫ γ
      ≡⟨⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ (_∙_) V g₂ g₁ ⟫ (func (lock-fmap μ (const-substˡ Γ ((_∙_) C f₂ f₁))) {v₃} γ)
      ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ (_∙_) V g₂ g₁ ⟫_) helper ⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ (_∙_) V g₂ g₁ ⟫ (func (lock-fmap μ (const-substˡ Γ f₁)) (func (lock-fmap μ (const-substˡ Γ f₂)) γ))
      ≡⟨ ctx-comp (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₁ ⟫ 
          ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫ 
            (func (lock-fmap μ (const-substˡ Γ f₁)) 
              (func (lock-fmap μ (const-substˡ Γ f₂)) {v₃} γ)))
      ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₁ ⟫_) (_⇒_.naturality (lock-fmap μ (const-substˡ Γ f₁))) ⟩
        (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₁ ⟫ 
          (func (lock-fmap μ (const-substˡ Γ f₁)) {v₂} 
            ((Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫ 
              (func (lock-fmap μ (const-substˡ Γ f₂)) {v₃} γ)))
      ≡⟨⟩
        temp-ctx Γ ⟪ [ f₁ , g₁ ] ⟫ (temp-ctx Γ ⟪ [ f₂ , g₂ ] ⟫ γ) ∎
  {-
    RHS: 
      ctx-comp (temp-ctx Γ) {[ c₁ , v₁ ]} {[ c₂ , v₂ ]} {[ c₃ , v₃ ]} {[ f₁ , g₁ ]} {[ f₂ , g₂ ]} {γ : Γ ⟨ c₃ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₃ ⟩}
    : ctx-hom (temp-ctx Γ) ([ f₂ , g₂ ] ∙ [ f₁ , g₁ ]) γ ≡ ctx-hom (temp-ctx Γ) [ f₁ , g₁ ] (ctx-hom (temp-ctx Γ) [ f₂ , g₂ ] γ)

                f₁                    f₂
    c₁ ------------------ c₂ -----------------→ c₃
    v₁ ------------------ v₂ -----------------→ v₃
                g₁                    g₂


                                [ c₁ , v₁ ]                    [ c₂ , v₁ ]                   [ c₃ , v₁ ]
                                    ↑                                  
                                    |                             
                                    | func (lock-fmap μ (const-substˡ Γ f₁)) {v₂}                             
                                [ c₁ , v₂ ] ←----------------- [ c₂ , v₂ ]                   [ c₃ , v₂ ]
                                    ↑                              ↑
    (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫_ |                              | Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g₂ ⟫_
                                    |                              | 
                                [ c₁ , v₃ ] ←----------------- [ c₂ , v₃ ] ←----------------- [ c₃ , v₃ ]
                                      func (lock-fmap μ (const-substˡ Γ f₁)) {v₃} 
  -}
  {-      
        ctx-map-cong (⊚-comp-const-substˡ {D = V} Γ f₁ f₂)
      : lock-fmap μ (const-substˡ Γ (f₂ ∙ f₁)) ≅ˢ lock-fmap μ (const-substˡ Γ f₁ ⊚ const-substˡ Γ f₂)

        lock-fmap-⊚ μ (const-substˡ Γ f₁) (const-substˡ Γ f₂)
      : lock-fmap μ (const-substˡ Γ f₁ ⊚ const-substˡ Γ f₂) ≡ˢ lock-fmap μ (const-substˡ Γ f₁) ⊚ lock-fmap μ (const-substˡ Γ f₂)

        ≅ˢ-trans (ctx-map-cong (⊚-comp-const-substˡ {D = V} Γ f₁ f₂)) (lock-fmap-⊚ μ (const-substˡ Γ f₁) (const-substˡ Γ f₂))
      : lock-fmap μ (const-substˡ Γ (f₂ ∙ f₁)) ≅ˢ lock-fmap μ (const-substˡ Γ f₁) ⊚ lock-fmap μ (const-substˡ Γ f₂)
        eq (≅ˢ-trans (ctx-map-cong (⊚-comp-const-substˡ {D = V} Γ f₁ f₂)) (lock-fmap-⊚ μ (const-substˡ Γ f₁) (const-substˡ Γ f₂))) γ
      : func (lock-fmap μ (const-substˡ Γ (f₂ ∙ f₁))) γ ≡ func (lock-fmap μ (const-substˡ Γ f₁) ⊚ lock-fmap μ (const-substˡ Γ f₂)) γ
      = func (lock-fmap μ (const-substˡ Γ (f₂ ∙ f₁))) γ ≡ func (lock-fmap μ (const-substˡ Γ f₁)) (func (lock-fmap μ (const-substˡ Γ f₂)) γ)
  -}

{-
  σ : Δ ⇒ Γ @ C×W
  ---------------------------------------------
  temp-subst σ : temp-ctx Δ ⇒ temp-ctx Γ @ C×V

  First take a projection of the given substitution σ : Δ ⇒ Γ @ C×W 
  along with c to obtain a substitution @ W; then apply the action 
  of modality μ on this new subsitutiton to obtain a substitution @ V. 
-}
temp-subst : ∀ {Δ Γ} → Δ ⇒ Γ → temp-ctx Δ ⇒ temp-ctx Γ
func (temp-subst σ) {[ c , v ]} = func (lock-fmap μ (fix-substˡ σ c)) {v}
_⇒_.naturality (temp-subst {Δ} {Γ} σ) {x = [ c₁ , v₁ ]} {y = [ c₂ , v₂ ]} {f = [ f , g ]} {δ = γ} =
  {-
                                    [ f , g ]
                    [ c₁ , v₁ ] -----------------→ [ c₂ , v₂ ]

                                    temp-ctx Δ ⟪ [ f , g ] ⟫_
        temp-ctx Δ ⟨ [ c₁ , v₁ ] ⟩ ←------------------------- temp-ctx Δ ⟨ [ c₂ , v₂ ] ⟩ ∋ γ
                       ∣                                                  ∣
    func {[ c₁ , v₁ ]} ∣                                                  ∣ func {[ c₂ , v₂ ]}
                       ↓                                                  ↓
        temp-ctx Γ ⟨ [ c₁ , v₁ ] ⟩ ←------------------------- temp-ctx Γ ⟨ [ c₂ , v₂ ] ⟩
                                    temp-ctx Γ ⟪ [ f , g ] ⟫_

      temp-ctx Γ ⟪ [ f , g ] ⟫ (func (temp-subst σ) {[ c₂ , v₂ ]} γ) ≡ func (temp-subst σ) {[ c₁ , v₁ ]} (temp-ctx Δ ⟪ [ f , g ] ⟫ γ)


      (func (lock-fmap μ (fix-substˡ σ c₂)) {v₂} : Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ → Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
      (func (lock-fmap μ (const-substˡ Γ f)) {v₂} : Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ → Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_ : Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ → Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩

      func (lock-fmap μ (const-substˡ Δ f)) {v₂} : Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ → Δ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
      (Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_ : Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ → Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩
      func (lock-fmap μ (fix-substˡ σ c₁)) {v₁} : Δ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ → Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩
                                                                                    
                                                      Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------------ Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ ∋ γ
                                                     / |                                                            / |             
                                                   /   |                                                          / (func (lock-fmap μ (fix-substˡ σ c₂)) {v₂}
                                                 ∟     |            (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_              ∟     |
                                    Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------------ Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
                                                |      ↓                                                       |      ↓
                                                |      Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------- | ---- Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩             
    (func (lock-fmap μ (const-substˡ Γ f)) {v₁} |     /                                                        |     / 
                                                |   / func (lock-fmap μ (fix-substˡ σ c₁)) {v₁}                | (func (lock-fmap μ (const-substˡ Γ f)) {v₂}
                                                ↓ ∟                                                            ↓ ∟
                                    Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₁ ⟩ ←------------------------------ Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
                                                                  (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_
                                  (func (lock-fmap μ (const-substˡ Δ f)) {v₂}
  -}
  {-
    Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩ ⟨ v₂ ⟩ ←------------------------------------------- Δ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩      
                |                                                                         |
                | (func (lock-fmap μ (fix-substˡ σ c₁)) {v₂}                              | (func (lock-fmap μ (fix-substˡ σ c₂)) {v₂}
                ↓                                                                         ↓
    Γ ⟨ c₁ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩ ←------------------------------------------- Γ ⟨ c₂ ⟩ˡ ,lock ⟨ μ ⟩ ⟨ v₂ ⟩
                                   (func (lock-fmap μ (const-substˡ Γ f)) {v₂}

      func (lock-fmap μ (const-substˡ Γ f)) {v₂} (func (lock-fmap μ (fix-substˡ σ c₂)) {v₂} γ)
    ≡⟨⟩
      func (lock-fmap μ (const-substˡ Γ f) ⊚ lock-fmap μ (fix-substˡ σ c₂)) {v₂} γ
    ≡⟨ eq (sym (lock-fmap-⊚ μ (const-substˡ Γ f) (fix-substˡ σ c₂))) {v₂} γ ⟩
      func (lock-fmap μ ((const-substˡ Γ f) ⊚ (fix-substˡ σ c₂))) γ

    eq (lock-fmap-cong μ (fix-substˡ σ c₁) (const-substˡ Δ f)) γ : func (lock-fmap μ ((fix-substˡ σ c₁) ⊚ (const-substˡ Δ f))) γ ≡ func (lock-fmap μ (fix-substˡ σ c₁)) {v₂} (func (lock-fmap μ (const-substˡ Δ f)) {v₂} γ)
  -}
  begin
      temp-ctx Γ ⟪ [ f , g ] ⟫ (func (temp-subst σ) {[ c₂ , v₂ ]} γ)
    ≡⟨⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
        (func (lock-fmap μ (const-substˡ Γ f)) {v₂} 
          (func (lock-fmap μ (fix-substˡ σ c₂)) {v₂} γ))
    ≡˘⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-⊚ μ (const-substˡ Γ f) (fix-substˡ σ c₂)) {v₂} γ) ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
        (func (lock-fmap μ ((const-substˡ Γ f) ⊚ (fix-substˡ σ c₂))) γ)
    ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-cong μ fix-const-substˡ) γ) ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫  
        (func (lock-fmap μ ((fix-substˡ σ c₁) ⊚ (const-substˡ Δ f))) γ)
    ≡⟨ cong ((Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫_) (eq (lock-fmap-⊚ μ (fix-substˡ σ c₁) (const-substˡ Δ f)) γ) ⟩
      (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
        (func (lock-fmap μ (fix-substˡ σ c₁)) {v₂} 
          (func (lock-fmap μ (const-substˡ Δ f)) {v₂} γ))
    ≡⟨ _⇒_.naturality ((lock-fmap μ (fix-substˡ σ c₁))) ⟩
      func (lock-fmap μ (fix-substˡ σ c₁)) {v₁} 
        ((Δ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ 
          (func (lock-fmap μ (const-substˡ Δ f)) {v₂} γ))
    ≡⟨⟩
      func (temp-subst σ) {[ c₁ , v₁ ]} (temp-ctx Δ ⟪ [ f , g ] ⟫ γ) ∎
    where open ≡-Reasoning

temp-subst-cong : ∀ {Δ Γ : Ctx C×W} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → temp-subst σ ≅ˢ temp-subst τ
eq (temp-subst-cong σ=τ) = eq (lock-fmap-cong μ (fix-substˡ-cong σ=τ))

-- The action of `temp-ctx` on substitutions preserves identity morphisms.
temp-subst-id : ∀ {Γ : Ctx C×W} → temp-subst (id-subst Γ) ≅ˢ id-subst (temp-ctx Γ)
eq temp-subst-id = eq (≅ˢ-trans (lock-fmap-cong μ fix-substˡ-id) (lock-fmap-id μ))

-- The action of `temp-ctx` on substitutions commutes with the composition operation of Psh(C×W).
temp-subst-⊚ : ∀ {Δ Γ Θ : Ctx C×W} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 temp-subst (τ ⊚ σ) ≅ˢ temp-subst τ ⊚ temp-subst σ
eq (temp-subst-⊚ τ σ) = eq (≅ˢ-trans (lock-fmap-cong μ (fix-substˡ-⊚ τ σ)) 
        (lock-fmap-⊚ μ (fix-substˡ τ _) (fix-substˡ σ _)))

-- A proof that `temp-ctx : CtxOp C×W C×V` is a functor
instance
  temp-ctx-is-functor : IsCtxFunctor temp-ctx
  ctx-map {{temp-ctx-is-functor}} = temp-subst
  ctx-map-cong {{temp-ctx-is-functor}} = temp-subst-cong
  ctx-map-id {{temp-ctx-is-functor}} = temp-subst-id
  ctx-map-⊚ {{temp-ctx-is-functor}} = temp-subst-⊚

--------------------------------------------------
-- todo: μ̃ : Modality C×V C×W
-- temp-ty : Ty (temp-ctx Γ) → Ty Γ
-- temp-ty T ⟨ [ c , w ] , γ ⟩ = {!   !}
-- temp-ty T ⟪ [ f , g ] , eγ ⟫ = ?
-- ty-cong (temp-ty T) = ?
-- ty-id (temp-ty T) = ?
-- ty-comp (temp-ty T) = ?
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



 