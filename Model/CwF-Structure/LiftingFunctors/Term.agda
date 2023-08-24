--------------------------------------------------
-- In this file we show that a functor from base categories C to D
--   can be lifted to the term part of a dependent right adjoint
--   from Psh(C) to PSh(D).
--------------------------------------------------

open import Model.BaseCategory
open import Model.Functor

module Model.CwF-Structure.LiftingFunctors.Term {C D : BaseCategory} (F : Functor C D) where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.CwF-Structure.LiftingFunctors.Context F
open import Model.CwF-Structure.LiftingFunctors.Type F

open BaseCategory

tm-lift : {Γ : Ctx D} {T : Ty (F*-ctx Γ)} → Tm (F*-ctx Γ) T → Tm Γ (ty-lift T)
(tm-lift t) ⟨ d , γ ⟩' = t [ 𝝶 γ ]'
naturality (tm-lift {Γ} t) f eγ = tm-≅-to-≡ (record { eq = λ g → naturality t (hom-id C) (trans (ctx-id (F*-ctx Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ g ⟫_) eγ))) })

tm-lift-cong : {Γ : Ctx D} {T : Ty (F*-ctx Γ)} {t t' : Tm (F*-ctx Γ) T} →
                t ≅ᵗᵐ t' → tm-lift t ≅ᵗᵐ tm-lift t'
eq (tm-lift-cong t=t') γ = tm-≅-to-≡ (record { eq = λ _ → eq t=t' _ })

tm-lift-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (F*-ctx Γ)} (t : Tm (F*-ctx Γ) T) →
                  (tm-lift t) [ σ ]' ≅ᵗᵐ ι[ ty-lift-mod-natural σ ] tm-lift (t [ F*-subst σ ]')
eq (tm-lift-natural {Γ = Γ} σ {T} t) {d} γ = tm-≅-to-≡ proof
  where
    proof : (tm-lift t [ σ ]') ⟨ d , γ ⟩' 
              ≅ᵗᵐ
            (ι[ ty-lift-mod-natural σ ] tm-lift (t [ F*-subst σ ]')) ⟨ d , γ ⟩'
    eq proof g = trans (sym (naturality t (hom-id C) (trans (ctx-id (F*-ctx Γ)) (eq (F*-subst-𝝶 {Γ = Γ} {σ}) g))))
                (trans (eq (ι-trans (≅ᵗʸ-sym (ty-F*-subst-𝝶 σ _)) (ty-subst-comp T _ _) (t [ _ ⊚ _ ]')) g)
                       (eq (ι-cong (≅ᵗʸ-sym (ty-F*-subst-𝝶 σ _)) (≅ᵗᵐ-sym (tm-subst-comp t _ _))) g))

tm-lift-ι : {Γ : Ctx D} {T S : Ty (F*-ctx Γ)} (T=S : T ≅ᵗʸ S) (t : Tm (F*-ctx Γ) S) →
            ι[ ty-lift-mod-cong T=S ] tm-lift t ≅ᵗᵐ tm-lift (ι[ T=S ] t)
eq (tm-lift-ι T=S t) γ = tm-≅-to-≡ (ι-subst-commute (𝝶 γ) T=S t)

tm-lift⁻¹ : {Γ : Ctx D} {T : Ty (F*-ctx Γ)} → Tm Γ (ty-lift T) → Tm (F*-ctx Γ) T
(tm-lift⁻¹ {Γ} {T} t) ⟨ c , g ⟩' = ty-ctx-subst T (ctx-id Γ) (t ⟨ ob F c , g ⟩' ⟨ c , hom-id D ⟩')
naturality (tm-lift⁻¹ {Γ} {T} t) {c₁} {c₂} {g₂} f eγ = trans (sym (ty-comp T))
                                                      (trans (ty-cong T ((trans (hom-idᵒ C) (trans (sym (hom-idʳ C)) (∙assoc C)))))
                                                      (trans (ty-comp T)
                                                      (trans (cong (T ⟪ hom-id C ∙[ C ] hom-id C , _ ⟫_) (naturality (t ⟨ ob F c₂ , g₂ ⟩') f (hom-idᵒ D)))
                                                      (trans (ty-comp T)
                                                              (cong (T ⟪ hom-id C , trans (ctx-id (F*-ctx Γ)) (ctx-id Γ) ⟫_) (cong (_⟨ c₁ , hom-id D {ob F c₁} ⟩') (naturality t (hom F f) eγ)))))))

tm-lift⁻¹-cong : {Γ : Ctx D} {T : Ty (F*-ctx Γ)} {t t' : Tm Γ (ty-lift T)} →
                  t ≅ᵗᵐ t' → tm-lift⁻¹ t ≅ᵗᵐ tm-lift⁻¹ t'
eq (tm-lift⁻¹-cong {Γ} {T} t=t') {c} g = cong (ty-ctx-subst T (ctx-id Γ)) (cong (_⟨ c , hom-id D ⟩') (eq t=t' g))

tm-lift-mod-β : {Γ : Ctx D} {T : Ty (F*-ctx Γ)} (t : Tm (F*-ctx Γ) T) →
                tm-lift⁻¹ (tm-lift t) ≅ᵗᵐ t
eq (tm-lift-mod-β {Γ} t) g = naturality t (hom-id C) (trans (ctx-id (F*-ctx Γ)) (ctx-id Γ))

tm-lift-mod-η : {Γ : Ctx D} {T : Ty (F*-ctx Γ)} (t : Tm Γ (ty-lift T)) →
                tm-lift (tm-lift⁻¹ t) ≅ᵗᵐ t
eq (tm-lift-mod-η {Γ} {T} t) {d} γ = tm-≅-to-≡ proof
  where
    proof : tm-lift (tm-lift⁻¹ t) ⟨ d , γ ⟩' ≅ᵗᵐ t ⟨ d , γ ⟩'
    eq proof {c} g = trans (cong (T ⟪ hom-id C , trans (ctx-id (F*-ctx Γ)) (ctx-id Γ) ⟫_) (cong (_⟨ c , hom-id D ⟩') (sym (naturality t g refl))))
                    (trans (sym (ty-comp T))
                    (trans (ty-cong T (hom-idˡ C))
                           (naturality (t ⟨ d , γ ⟩') (hom-id C)(trans (cong (category-composition D (g ∙[ D ] (hom-id D))) (id-law F)) (trans (hom-idʳ D) (hom-idʳ D))))))
