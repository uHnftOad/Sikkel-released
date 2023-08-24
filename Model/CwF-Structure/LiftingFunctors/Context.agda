--------------------------------------------------
-- In this file we show that a functor from base categories C to D
--   can be lifted to a "strict" CwF endomorphism from Psh(D) to Psh(C).
--------------------------------------------------

open import Model.BaseCategory
open import Model.Functor

module Model.CwF-Structure.LiftingFunctors.Context {C D : BaseCategory} (F : Functor C D) where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure

open BaseCategory

F*-ctx : Ctx D → Ctx C
F*-ctx Γ ⟨ c ⟩ = Γ ⟨ ob F c ⟩
F*-ctx Γ ⟪ f ⟫ γ = Γ ⟪ hom F f ⟫ γ
ctx-id (F*-ctx Γ) {γ = γ} = trans (cong (Γ ⟪_⟫ γ) (id-law F)) (ctx-id Γ)
ctx-comp (F*-ctx Γ) {γ = γ} = trans (cong (Γ ⟪_⟫ γ) (comp-law F)) (ctx-comp Γ)

F*-subst : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) → F*-ctx Δ ⇒ F*-ctx Γ
func (F*-subst σ) {c} = func σ {ob F c}
naturality (F*-subst σ) {f = f} = naturality σ {f = hom F f}

F*-subst-cong : {Δ : Ctx D} {Γ : Ctx D} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → F*-subst σ ≅ˢ F*-subst τ
eq (F*-subst-cong σ=τ) _ = eq σ=τ _

F*-subst-id : {Γ : Ctx D} → F*-subst (id-subst Γ) ≅ˢ id-subst (F*-ctx Γ)
eq F*-subst-id _ = refl

F*-subst-comp : {Δ : Ctx D} {Γ : Ctx D} {Θ : Ctx D} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                  F*-subst (τ ⊚ σ) ≅ˢ F*-subst τ ⊚ F*-subst σ
eq (F*-subst-comp τ σ) _ = refl

instance
  F*-is-functor : IsCtxFunctor F*-ctx
  ctx-map {{F*-is-functor}} = F*-subst
  ctx-map-cong {{F*-is-functor}} = F*-subst-cong
  ctx-map-id {{F*-is-functor}} = F*-subst-id
  ctx-map-⊚ {{F*-is-functor}} = F*-subst-comp

F* : CtxFunctor D C
ctx-op F* = F*-ctx
is-functor F* = F*-is-functor
