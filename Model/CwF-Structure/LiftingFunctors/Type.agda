--------------------------------------------------
-- In this file we show that a functor from base categories C to D
--   can be lifted to the type part of a dependent right adjoint
--   from Psh(C) to PSh(D).
--------------------------------------------------

open import Model.BaseCategory
open import Model.Functor

module Model.CwF-Structure.LiftingFunctors.Type {C D : BaseCategory} (F : Functor C D) where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.CwF-Structure.LiftingFunctors.Context F

open BaseCategory

𝝶 : {Γ : Ctx D} {d : Ob D} → Γ ⟨ d ⟩ → F*-ctx (𝕪 d) ⇒ F*-ctx Γ
𝝶 {Γ} {d} γ = F*-subst {𝕪 d} {Γ} (to-𝕪⇒* {D} {Γ} γ)

ty-lift : {Γ : Ctx D} → Ty (F*-ctx Γ) → Ty Γ
ty-lift T ⟨ d , γ ⟩ = Tm (F*-ctx (𝕪 d)) (T [ 𝝶 γ ])
(ty-lift {Γ} T ⟪ f , eγ ⟫ t) ⟨ c , g ⟩' = ty-ctx-subst T (trans (ctx-comp Γ) (cong (Γ ⟪ g ⟫_) eγ)) (t ⟨ c , f ∙[ D ] g ⟩')
  -- trans (ctx-comp Γ) (cong (Γ ⟪ g ⟫_) eγ) : Γ ⟪ f ∙[ D ] g ⟫ γ₂ ≡ Γ ⟪ g ⟫ γ₁
naturality (ty-lift {Γ} T ⟪ f , eγ ⟫ t) {γx = h₁} g eh = trans (sym (ty-comp T))
                                                        (trans (ty-cong T (hom-idᵒ C))
                                                        (trans (ty-comp T) 
                                                               (cong (T ⟪ hom-id C , trans (ctx-id (F*-ctx Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ h₁ ⟫_) eγ)) ⟫_) 
                                                                     (naturality t g (trans (∙assoc D) (cong (category-composition D f) eh))))))
ty-cong (ty-lift {Γ} T) {f = f} {f'} e-hom {eγ = eγ} {eγ'} {t} = tm-≅-to-≡ proof
  where
    proof : ty-lift T ⟪ f , eγ ⟫ t ≅ᵗᵐ ty-lift T ⟪ f' , eγ' ⟫ t
    eq proof g = 
      trans (cong (T ⟪ hom-id C , trans (ctx-id (F*-ctx Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ g ⟫_) eγ)) ⟫_) 
                  (sym (naturality t (hom-id C) ((trans (cong (category-composition D (f' ∙[ D ] g)) (id-law F)) (trans (hom-idʳ D) (cong (λ h → category-composition D h g) (sym e-hom))))))))
            (trans (sym (ty-comp T)) (ty-cong T (hom-idˡ C)))
ty-id (ty-lift {Γ} T) {γ = γ} {t} = tm-≅-to-≡ proof
  where
    proof : ty-lift T ⟪ hom-id D , ctx-id Γ ⟫ t ≅ᵗᵐ t
    eq proof g = trans (cong (T ⟪ hom-id C , trans (ctx-id (F*-ctx Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ g ⟫_) (ctx-id Γ))) ⟫_) 
                             (sym (naturality t (hom-id C) (trans (cong (category-composition D g) (id-law F)) (hom-idⁱ D)))))
                (trans (sym (ty-comp T))
                (trans (ty-cong T (hom-idˡ C)) 
                      (ty-id T)))
ty-comp (ty-lift {Γ} T) {f = f} {g} {eγ-zy = eγ-32} {eγ-21} {t} = tm-≅-to-≡ proof
  where
    open ≡-Reasoning
    proof : ty-lift T ⟪ g ∙[ D ] f , strong-ctx-comp Γ eγ-32 eγ-21 ⟫ t
              ≅ᵗᵐ
            ty-lift T ⟪ f , eγ-21 ⟫ ty-lift T ⟪ g , eγ-32 ⟫ t
    eq proof {c} h = trans (cong (T ⟪ hom-id C , trans (ctx-id (F*-ctx Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ h ⟫_) (strong-ctx-comp Γ eγ-32 eγ-21))) ⟫_) 
                                 (sym (naturality t (hom-id C) (trans (cong (category-composition D (g ∙[ D ] (f ∙[ D ] h))) (id-law F)) (trans (hom-idʳ D) (sym (∙assoc D)))))))
                    (trans (sym (ty-comp T))
                    (trans (ty-cong T refl) (ty-comp T)))

ty-lift-mod-cong : {Γ : Ctx D} {T S : Ty (F*-ctx Γ)} → T ≅ᵗʸ S → ty-lift T ≅ᵗʸ ty-lift S
func (from (ty-lift-mod-cong T=S)) {γ = γ} t = ι[ ty-subst-cong-ty (𝝶 γ) (≅ᵗʸ-sym T=S) ] t
naturality (from (ty-lift-mod-cong T=S)) = tm-≅-to-≡ (record { eq = λ _ → naturality (from T=S) })
func (to (ty-lift-mod-cong T=S)) {γ = γ} t = ι[ ty-subst-cong-ty (𝝶 γ) T=S ] t
naturality (to (ty-lift-mod-cong T=S)) = tm-≅-to-≡ (record { eq = λ _ → naturality (to T=S) })
eq (isoˡ (ty-lift-mod-cong T=S)) {γ = γ} t = tm-≅-to-≡ proof
  where
    open ≡-Reasoning
    proof : func (to (ty-lift-mod-cong T=S) ⊙ from (ty-lift-mod-cong T=S)) t ≅ᵗᵐ t
    eq proof {c} g =
      begin
        (ι[ ty-subst-cong-ty (𝝶 γ) T=S ]
          (ι[ ty-subst-cong-ty (𝝶 γ) (≅ᵗʸ-sym T=S) ] t))
            ⟨ c , g ⟩'
      ≡˘⟨ eq (ι-trans (ty-subst-cong-ty (𝝶 γ) T=S) (ty-subst-cong-ty (𝝶 γ) (≅ᵗʸ-sym T=S)) t) g ⟩ 
        func (to T=S ⊙ from T=S) (t ⟨ c , g ⟩')
      ≡⟨ eq (isoˡ T=S) (t ⟨ c , g ⟩') ⟩ 
        t ⟨ c , g ⟩' ∎
eq (isoʳ (ty-lift-mod-cong T=S)) {γ = γ} t = tm-≅-to-≡ proof
  where
    open ≡-Reasoning
    proof : func (from (ty-lift-mod-cong T=S) ⊙ to (ty-lift-mod-cong T=S)) t ≅ᵗᵐ t
    eq proof {c} g = 
      begin
        (ι[ ty-subst-cong-ty (𝝶 γ) (≅ᵗʸ-sym T=S) ]
          (ι[ ty-subst-cong-ty (𝝶 γ) T=S ] t))
            ⟨ c , g ⟩'
      ≡˘⟨ eq (ι-trans (ty-subst-cong-ty (𝝶 γ) (≅ᵗʸ-sym T=S)) (ty-subst-cong-ty (𝝶 γ) T=S) t) g ⟩ 
        func (from T=S ⊙ to T=S) (t ⟨ c , g ⟩')
      ≡⟨ eq (isoʳ T=S) (t ⟨ c , g ⟩') ⟩ 
        t ⟨ c , g ⟩' ∎

F*-subst-𝝶 : {Δ Γ : Ctx D} {σ : Δ ⇒ Γ} {d : Ob D} {γ : Δ ⟨ d ⟩} → 
                             F*-subst σ ⊚ 𝝶 γ ≅ˢ 𝝶 (func σ γ)
eq (F*-subst-𝝶 {σ = σ}) _ = sym (naturality σ)

ty-F*-subst-𝝶 : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) (T : Ty (F*-ctx Γ)) {d : Ob D} {γ : Δ ⟨ d ⟩} → 
                                T [ F*-subst σ ] [ 𝝶 γ ] ≅ᵗʸ T [ 𝝶 (func σ γ) ]
ty-F*-subst-𝝶 σ T {γ = γ} = ≅ᵗʸ-trans (ty-subst-comp T (F*-subst σ) (𝝶 γ)) (ty-subst-cong-subst F*-subst-𝝶 T)
  -- func (to (ty-F*-subst-𝝶 σ T)) s = T ⟪ hom-id C , _ ⟫ s
  
ty-lift-mod-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (F*-ctx Γ)} → 
                      (ty-lift T) [ σ ] ≅ᵗʸ ty-lift (T [ F*-subst σ ])
func (from (ty-lift-mod-natural σ)) t = ι[ ty-F*-subst-𝝶 σ _ ] t
naturality (from (ty-lift-mod-natural σ {T})) = tm-≅-to-≡ (record { eq = λ _ → trans (sym (ty-comp T)) (trans (ty-cong T refl) (ty-comp T)) })
func (to (ty-lift-mod-natural σ)) t = ι⁻¹[ ty-F*-subst-𝝶 σ _ ] t
naturality (to (ty-lift-mod-natural σ {T})) = tm-≅-to-≡ (record { eq = λ _ → trans (sym (ty-comp T)) (trans (ty-cong T refl) (ty-comp T)) })
eq (isoˡ (ty-lift-mod-natural σ)) t = tm-≅-to-≡ (ι-symˡ (ty-F*-subst-𝝶 σ _) t)
eq (isoʳ (ty-lift-mod-natural {Δ} {Γ} σ {T})) {d} {γ} t = tm-≅-to-≡ (ι-symʳ (ty-F*-subst-𝝶 σ _) t)
