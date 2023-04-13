--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
open import Model.BaseCategory
open import Model.Modality

module Applications.CombiningFeatures.Model.Modalities.Lift-general {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Nat
-- open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Product renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injectiveʳ)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure

open BaseCategory

C×V : BaseCategory
C×V = C ⊗ V
open Ctx C×V

C×W : BaseCategory
C×W = C ⊗ W

private
  variable
    c₁ c₂ : Ob C
    v₁ v₂ : Ob V
    w₁ w₂ : Ob W
    Γ Δ Θ : Ctx C×W


--------------------------------------------------
{- 
  μ : Modality V W
  ctx-functor μ : CtxFunctor W V
    with ctx-op (ctx-functor μ) : Ctx W → Ctx V
  --------------------------------------------------
  lock : CtxOp W V
  lock = ctx-op ctx-functor

  lock-fmap : {Δ Γ : Ctx W} → (Δ ⇒ Γ) → (lock Δ ⇒ lock Γ)
  lock-fmap = ctx-fmap ctx-functor

  lock-fmap-cong = ctx-fmap-cong ctx-functor

  lock-fmap-id = ctx-fmap-id ctx-functor

  lock-fmap-⊚ = ctx-fmap-⊚ ctx-functor
  --------------------------------------------------
  ⟨_∣_⟩ : {Γ : Ctx W} → Ty (lock Γ) → Ty Γ
  mod-cong : {Γ : Ctx W} {T S : Ty (lock Γ)} →
               T ≅ᵗʸ S → ⟨_∣_⟩ T ≅ᵗʸ ⟨_∣_⟩ S
  mod-natural : {Δ : Ctx W} {Γ : Ctx W} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} →
                  (⟨_∣_⟩ T) [ σ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap σ ])
  mod-intro : {Γ : Ctx W} {T : Ty (lock Γ)} → Tm (lock Γ) T → Tm Γ (⟨_∣_⟩ T)
  mod-intro-cong : {Γ : Ctx W} {T : Ty (lock Γ)} {t t' : Tm (lock Γ) T} →
                     t ≅ᵗᵐ t' → mod-intro t ≅ᵗᵐ mod-intro t'
  mod-intro-natural : {Δ Γ : Ctx W} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
                      (mod-intro t) [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ lock-fmap σ ]')
  mod-intro-ι : {Γ : Ctx W} {T S : Ty (lock Γ)} (T=S : T ≅ᵗʸ S) (t : Tm (lock Γ) S) →
                  ι[ mod-cong T=S ] mod-intro t ≅ᵗᵐ mod-intro (ι[ T=S ] t)
  mod-elim : {Γ : Ctx W} {T : Ty (lock Γ)} → Tm Γ (⟨_∣_⟩ T) → Tm (lock Γ) T
  mod-elim-cong : {Γ : Ctx W} {T : Ty (lock Γ)} {t t' : Tm Γ (⟨_∣_⟩ T)} →
                    t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
  mod-β : {Γ : Ctx W} {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
            mod-elim (mod-intro t) ≅ᵗᵐ t
  mod-η : {Γ : Ctx W} {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
            mod-intro (mod-elim t) ≅ᵗᵐ t
-}


--------------------------------------------------
-- todo: everything related to ctx-functor μ̃

temp-ctx : Ctx C×W → Ctx C×V
temp-ctx Γ ⟨ [ c , v ] ⟩ = (Γ ⟨ c ⟩ˡ) ,lock⟨ μ ⟩ ⟨ v ⟩
temp-ctx Γ ⟪ [ hom-id C , g ] ⟫ γ = (Γ ⟨ _ ⟩ˡ) ,lock⟨ μ ⟩ ⟪ g ⟫ γ
temp-ctx Γ ⟪ ( f , hom-id V ) ⟫ γ = lock-fmap μ (const-substˡ Γ f)
temp-ctx Γ ⟪ [ f , g ] ⟫ γ = temp-ctx Γ ⟪ [ hom-id C , g ] ⟫ (temp-ctx Γ ⟪ [ f , hom-id V ] ⟫ γ)
ctx-id (temp-ctx Γ) = ?
ctx-comp (temp-ctx Γ) = ?

-- temp-ctx Γ ⟪ [ z≤n {0} , g ] ⟫ γ = (now Γ ,lock⟨ μ ⟩) ⟪ g ⟫ γ
-- temp-ctx Γ ⟪ [ s≤s {m} ≤-refl , g ] ⟫ γ = temp-ctx (◄ Γ) ⟪ [ ≤-refl {m} , g ] ⟫ γ
-- temp-ctx Γ ⟪ [ m≤n , hom-id V ] ⟫ γ = lock-fmap μ (const-subst-slice Γ m≤n)
-- temp-ctx Γ ⟪ [ m≤n , g ] ⟫ γ = temp-ctx Γ ⟪ [ ≤-refl , g ] ⟫ (temp-ctx Γ ⟪ [ m≤n , hom-id V ] ⟫ γ) -- : temp-ctx Γ ⟨ [ n , y ] ⟩ → temp-ctx Γ ⟨ [ m , x ] ⟩
ctx-id (temp-ctx Γ) = {!   !}
ctx-comp (temp-ctx Γ) = {!   !}

-- temp-subst : 

--------------------------------------------------
-- todo: ⟨ μ̃ ∣_⟩ : Ty (lock Γ) → Ty Γ
-- temp-ty : Ty (temp-ctx Γ) → Ty Γ





