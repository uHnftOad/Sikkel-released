--------------------------------------------------
-- A functor from base categories C to D can be lifted 
--   to a modality from Psh(C) to Psh(D).
--------------------------------------------------

module Model.CwF-Structure.LiftingFunctors.Modality where

open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.CwF-Structure.LiftingFunctors.Context public
open import Model.CwF-Structure.LiftingFunctors.Type public
open import Model.CwF-Structure.LiftingFunctors.Term public
open import Model.BaseCategory
open import Model.Functor
open import Model.Modality

open BaseCategory

private
  variable
    C D E : BaseCategory

_*-ctx_ : Functor C D → Ctx D → Ctx C
F *-ctx Γ = F*-ctx F Γ

_*-subst_ : (F : Functor C D) {Δ : Ctx D} {Γ : Ctx D} → 
            (σ : Δ ⇒ Γ) → F *-ctx Δ ⇒ F *-ctx Γ
F *-subst σ = F*-subst F σ

fun-to-mod : Functor C D → Modality C D
ctx-functor (fun-to-mod F) = F* F
⟨_∣_⟩ (fun-to-mod F) = ty-lift F
mod-cong (fun-to-mod F) = ty-lift-mod-cong F
mod-natural (fun-to-mod F) = ty-lift-mod-natural F
mod-intro (fun-to-mod F) = tm-lift F
mod-intro-cong (fun-to-mod F) = tm-lift-cong F
mod-intro-natural (fun-to-mod F) = tm-lift-natural F
mod-intro-ι (fun-to-mod F) = tm-lift-ι F
mod-elim (fun-to-mod F) = tm-lift⁻¹ F
mod-elim-cong (fun-to-mod F) = tm-lift⁻¹-cong F
mod-β (fun-to-mod F) = tm-lift-mod-β F
mod-η (fun-to-mod F) = tm-lift-mod-η F


--------------------------------------------------
-- `fun-to-mod` preserves identities.

id-eq-lock : (Γ : Ctx C) → Γ ,lock⟨ fun-to-mod id-functor ⟩ ≅ᶜ Γ ,lock⟨ 𝟙 ⟩
from (id-eq-lock Γ) = MkSubst id refl
to (id-eq-lock Γ) = MkSubst id refl
eq (isoˡ (id-eq-lock Γ)) _ = refl
eq (isoʳ (id-eq-lock Γ)) _ = refl

id-eq-lock-natural-to : {Δ Γ : Ctx C} (σ : Δ ⇒ Γ) →
                        to (id-eq-lock Γ) ⊚ lock-fmap 𝟙 σ ≅ˢ lock-fmap (fun-to-mod id-functor) σ ⊚ to (id-eq-lock Δ)
eq (id-eq-lock-natural-to _) _ = refl

id-eq-mod-tyʳ : {Γ : Ctx C} (T : Ty (Γ ,lock⟨ fun-to-mod id-functor ⟩)) → 
                ⟨ fun-to-mod id-functor ∣ T ⟩ ≅ᵗʸ ⟨ 𝟙 ∣ T [ to (id-eq-lock Γ) ] ⟩
func (from (id-eq-mod-tyʳ {C} {Γ} T)) {c} t = ty-ctx-subst T (ctx-id Γ) (t ⟨ c , hom-id C ⟩')
naturality (from (id-eq-mod-tyʳ {C} {Γ} T)) {f = f} {t = t} = trans (sym (ty-comp T))
                                                             (trans (ty-cong T (trans (hom-idᵒ C) (trans (sym (hom-idʳ C)) (∙assoc C))))
                                                             (trans (ty-comp T)
                                                             (trans (ty-comp T)
                                                                    (cong (λ s → ty-ctx-subst T (ctx-id Γ) (ty-ctx-subst T (trans (ctx-comp Γ) (cong (Γ ⟪ hom-id C ⟫_) _)) s)) (naturality t f (hom-idᵒ C))))))
func (to (id-eq-mod-tyʳ T)) t ⟨ _ , g ⟩' = T ⟪ g , refl ⟫ t
naturality (func (to (id-eq-mod-tyʳ T)) t) f eγ = trans (sym (ty-comp T)) (ty-cong T eγ)
naturality (to (id-eq-mod-tyʳ {C} {Γ} T)) {f = f} {eγ = eγ} {t} = tm-≅-to-≡ (record { eq = λ _ → trans (sym (ty-comp T)) (trans (ty-cong T (hom-idʳ C)) (ty-comp T))})
eq (isoˡ (id-eq-mod-tyʳ {C} T)) t = tm-≅-to-≡ (record { eq = λ g → trans (sym (ty-comp T)) (trans (ty-cong T (hom-idˡ C)) (naturality t g (hom-idˡ C))) })
eq (isoʳ (id-eq-mod-tyʳ {C} T)) t = trans (sym (ty-comp T)) (trans (ty-cong T (hom-idˡ C)) (ty-id T))

fun-to-mod-id : fun-to-mod (id-functor {C}) ≅ᵐ 𝟙
eq-lock fun-to-mod-id = id-eq-lock
eq-lock-natural-to fun-to-mod-id = id-eq-lock-natural-to
eq-mod-tyʳ fun-to-mod-id = id-eq-mod-tyʳ


--------------------------------------------------
-- `fun-to-mod` commutes with composition.

comp-eq-lock : {G : Functor D E} {F : Functor C D} (Γ : Ctx E) → 
               Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩ 
                 ≅ᶜ 
               Γ ,lock⟨ fun-to-mod G ⓜ fun-to-mod F ⟩
from (comp-eq-lock Γ) = MkSubst id refl
to (comp-eq-lock Γ) = MkSubst id refl
eq (isoˡ (comp-eq-lock Γ)) _ = refl
eq (isoʳ (comp-eq-lock Γ)) _ = refl

comp-eq-lock-natural-to : {G : Functor D E} {F : Functor C D} {Δ Γ : Ctx E} (σ : Δ ⇒ Γ) →
                          to (comp-eq-lock Γ) ⊚ lock-fmap (fun-to-mod G ⓜ fun-to-mod F) σ 
                            ≅ˢ 
                          lock-fmap (fun-to-mod (G ∘ᶠ F)) σ ⊚ to (comp-eq-lock Δ)
eq (comp-eq-lock-natural-to _) _ = refl

comp-eq-mod-tyʳ : {G : Functor D E} {F : Functor C D} {Γ : Ctx E} (T : Ty (Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩)) → 
                  ⟨ fun-to-mod (G ∘ᶠ F) ∣ T ⟩ 
                    ≅ᵗʸ 
                  ⟨ fun-to-mod G ⓜ fun-to-mod F ∣ T [ to (comp-eq-lock Γ) ] ⟩
func (from (comp-eq-mod-tyʳ {G = G} {F} {Γ} T)) {e} {γ} t =
  ι[ mod-natural (fun-to-mod F) (𝝶 G {Γ} {e} γ) ]
    (mod-intro (fun-to-mod F) 
      (ι[ ty-subst-comp T (to (comp-eq-lock Γ)) (ctx-fmap (ctx-functor (fun-to-mod F)) (𝝶 G γ)) ] 
        (ι[ ty-subst-cong-subst ((record { eq = λ _ → refl })) T ] 
          (ι[ ≅ᵗʸ-sym (ty-subst-comp T (𝝶 (G ∘ᶠ F) γ) (to (comp-eq-lock (𝕪 e)))) ] 
            (t [ to (comp-eq-lock (𝕪 e)) ]')))))
  {- ≅ᵗᵐ ι[ iso₃ ] mod-intro (fun-to-mod F) (t [ to (comp-eq-lock (𝕪 e)) ]')
    where 
      iso₁ : to (comp-eq-lock Γ) ⊚ F*-subst F (𝝶 G {Γ} γ)
              ≅ˢ
             𝝶 (G ∘ᶠ F) γ ⊚ to (comp-eq-lock (𝕪 e))
      iso₁ = record { eq = λ _ → refl }

      iso₂ : ty-lift F (T [ to (comp-eq-lock Γ) ] [ F*-subst F (𝝶 G γ) ])
              ≅ᵗʸ
             ty-lift F (T [ 𝝶 (G ∘ᶠ F) γ ] [ to (comp-eq-lock (𝕪 e)) ])
      iso₂ = mod-cong (fun-to-mod F) (≅ᵗʸ-trans (ty-subst-comp T _ _) (≅ᵗʸ-trans (ty-subst-cong-subst iso₁ T) (≅ᵗʸ-sym (ty-subst-comp T _ _))))

      iso₃ : (ty-lift F (T [ to (comp-eq-lock Γ) ])) [ 𝝶 G γ ]
              ≅ᵗʸ
             ty-lift F (T [ 𝝶 (G ∘ᶠ F) γ ] [ to (comp-eq-lock (𝕪 e)) ])
      iso₃ = ≅ᵗʸ-trans (mod-natural (fun-to-mod F) (𝝶 G γ)) iso₂
    ---------------------
    F*-ctx (G ∘ᶠ F) (𝕪 e) ⊢ t : T [ 𝝶 (G ∘ᶠ F) γ ] @ C
    ---------------------
    F*-ctx F (F*-ctx G (𝕪 e)) ⊢ t [ to (comp-eq-lock (𝕪 e)) ]' : T [ 𝝶 (G ∘ᶠ F) γ ] [ to (comp-eq-lock (𝕪 e)) ] @ C
    ---------------------
    F*-ctx G (𝕪 e) ⊢ tm-lift (t [ to (comp-eq-lock (𝕪 e)) ]') : ty-lift F (T [ 𝝶 (G ∘ᶠ F) γ ] [ to (comp-eq-lock (𝕪 e)) ]) @ D
    ---------------------
    F*-ctx G (𝕪 e) ⊢ ι[ helper₃ ] tm-lift (t [ to (comp-eq-lock (𝕪 e)) ]') : (ty-lift F (T [ to (comp-eq-lock Γ) ])) [ 𝝶 G γ ] @ D
  -}
naturality (from (comp-eq-mod-tyʳ {D} {E} {C} {G} {F} {Γ} T)) {f = f} {eγ = eγ} {t} = tm-≅-to-≡ (record { eq = λ γ → tm-≅-to-≡ (record { eq = λ g → proof } ) }) 
  where
    open ≡-Reasoning
    proof : ∀ {e} {γ} {c} {g} → 
              ((ty-lift G (ty-lift F (T [ to (comp-eq-lock Γ) ])) ⟪ f , eγ ⟫ 
                func (from (comp-eq-mod-tyʳ {G = G} T)) t) ⟨ e , γ ⟩') ⟨ c , g ⟩'
                ≡
              (func (from (comp-eq-mod-tyʳ {G = G} T)) (ty-lift (G ∘ᶠ F) T ⟪ f , eγ ⟫ t) ⟨ e , γ ⟩') ⟨ c , g ⟩'
    proof {e} {γ} {c} {g} = trans (sym (ty-comp T))
                           (trans (sym (ty-comp T))
                           (trans (ty-cong T (sym (hom-idˡ C)))
                           (trans (ty-comp T)
                           (trans (cong (T ⟪ hom-id C ∙[ C ] (hom-id C ∙[ C ] hom-id C) , strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ γ ∙[ E ] (hom G g) ⟫_) eγ))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) refl) _) ⟫_) 
                                        (naturality t (hom-id C {c}) ((trans (cong (category-composition E ((f ∙[ E ] γ) ∙[ E ] (hom G (hom-id D ∙[ D ] g)))) (id-law (G ∘ᶠ F))) (trans (hom-idʳ E) (trans (cong (category-composition E (f ∙[ E ] γ)) (cong (hom G) (hom-idˡ D))) (∙assoc E)))))))
                           (trans (ty-comp T) 
                           (ty-comp T))))))
func (to (comp-eq-mod-tyʳ {G = G} {F} {Γ} T)) {e} {γ} t = 
  ι[ ty-subst-cong-subst {Δ = F*-ctx (G ∘ᶠ F) (𝕪 e)} {Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩} {𝝶 (G ∘ᶠ F) γ} {to (comp-eq-lock Γ) ⊚ F*-subst F (𝝶 G γ) ⊚ from (comp-eq-lock (𝕪 e))} (record { eq = λ _ → refl }) T ]
    ι[ ty-subst-cong-subst {Δ = F*-ctx (G ∘ᶠ F) (𝕪 e)} {Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩} {to (comp-eq-lock Γ) ⊚ F*-subst F (𝝶 G γ) ⊚ from (comp-eq-lock (𝕪 e))} {to (comp-eq-lock Γ) ⊚ (F*-subst F (𝝶 G γ) ⊚ from (comp-eq-lock (𝕪 e)))} ⊚-assoc T ]
      ι[ ≅ᵗʸ-sym (ty-subst-comp T (to (comp-eq-lock Γ)) (F*-subst F (𝝶 G γ) ⊚ from (comp-eq-lock (𝕪 e)))) ]
        ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (comp-eq-lock Γ) ]) (F*-subst F (𝝶 G γ)) (from (comp-eq-lock (𝕪 e)))) ]
          ((tm-lift⁻¹ F (ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t)) 
            [ from (comp-eq-lock (𝕪 e)) ]')
  {-
    ≅ᵗᵐ ι[ helper₂ ] ((tm-lift⁻¹ F (ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t)) [ from (comp-eq-lock (𝕪 e)) ]')
      where
        helper₁ : 𝝶 (G ∘ᶠ F) γ
                    ≅ˢ
                  to (comp-eq-lock Γ) ⊚ F*-subst F (𝝶 G γ) ⊚ from (comp-eq-lock (𝕪 e))
        eq helper₁ {c} g = refl

        helper₂ : T [ 𝝶 (G ∘ᶠ F) γ ] ≅ᵗʸ T [ to (comp-eq-lock Γ) ] [ F*-subst F (𝝶 G γ) ] [ from (comp-eq-lock (𝕪 e)) ]
        helper₂ = ≅ᵗʸ-trans (ty-subst-cong-subst helper₁ T) 
                (≅ᵗʸ-trans (ty-subst-cong-subst ⊚-assoc T) 
                (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-comp T (to (comp-eq-lock Γ)) (F*-subst F (𝝶 G γ) ⊚ from (comp-eq-lock (𝕪 e))))) 
                            (≅ᵗʸ-sym (ty-subst-comp (T [ to (comp-eq-lock Γ) ]) (F*-subst F (𝝶 G γ)) (from (comp-eq-lock (𝕪 e)))))))

    ---------------------
    Γ ⊢ t : ty-lift G (ty-lift F (T [ to (comp-eq-lock Γ) ])) ⟨ e , γ ⟩ = Tm (F*-ctx G (𝕪 e)) ((ty-lift F (T [ to (comp-eq-lock Γ) ])) [ 𝝶 G γ ])
    ---------------------
    F*-ctx G (𝕪 e) ⊢ t : (ty-lift F (T [ to (comp-eq-lock Γ) ])) [ 𝝶 G γ ] @ D
      -- where 
      --   F*-ctx F (F*-ctx G Γ) ⊢ T [ to (comp-eq-lock Γ) ] @ C
      --   F*-ctx G Γ ⊢ ty-lift F (T [ to (comp-eq-lock Γ) ]) @ D
      --   F*-ctx G (𝕪 e) ⊢ (ty-lift F (T [ to (comp-eq-lock Γ) ])) [ 𝝶 G γ ] ≅ᵗʸ ty-lift F (T [ to (comp-eq-lock Γ) ] [ F*-subst F (𝝶 G γ) ])
    ---------------------
    F*-ctx G (𝕪 e) ⊢ ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t : ty-lift F (T [ to (comp-eq-lock Γ) ] [ F*-subst F (𝝶 G γ) ])
    ---------------------
    F*-ctx F (F*-ctx G (𝕪 e)) ⊢ tm-lift⁻¹ F (ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t) : T [ to (comp-eq-lock Γ) ] [ F*-subst F (𝝶 G γ) ] @ C
    ---------------------
    F*-ctx (G ∘ᶠ F) (𝕪 e) ­⊢ (tm-lift⁻¹ F (ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t)) [ from (comp-eq-lock (𝕪 e)) ]' : T [ to (comp-eq-lock Γ) ] [ F*-subst F (𝝶 G γ) ] [ from (comp-eq-lock (𝕪 e)) ] @ C
    ---------------------
    F*-ctx (G ∘ᶠ F) (𝕪 e) ­⊢ ι[ helper₂ ] ((tm-lift⁻¹ F (ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t)) [ from (comp-eq-lock (𝕪 e)) ]' : T [ 𝝶 (G ∘ᶠ F) γ ] @ C
    ---------------------
    Γ ⊢ ι[ helper₂ ] ((tm-lift⁻¹ F (ι⁻¹[ mod-natural (fun-to-mod F) (𝝶 G γ) ] t)) [ from (comp-eq-lock (𝕪 e)) ]' : ty-lift (G ∘ᶠ F) T ⟨ e , γ ⟩
  -}
naturality (to (comp-eq-mod-tyʳ {D} {E} {C} {G} {F} {Γ} T)) {y = e₂} {f} {γ₂} {eγ = eγ} {t} = tm-≅-to-≡ (record { eq = λ γ → proof }) 
  where
    proof : ∀ {e} {γ} → (ty-lift (G ∘ᶠ F) T ⟪ f , eγ ⟫ func (to (comp-eq-mod-tyʳ T)) t) ⟨ e , γ ⟩' 
                          ≡ 
                        func (to (comp-eq-mod-tyʳ T)) (ty-lift G (ty-lift F (T [ to (comp-eq-lock Γ) ])) ⟪ f , eγ ⟫ t) ⟨ e , γ ⟩'
    proof {e} {γ} = trans (sym (trans (ty-comp T) (trans (ty-comp T) (trans (ty-comp T) (ty-comp T))))) 
                   (trans (cong (T ⟪ hom-id C ∙[ C ] (hom-id C ∙[ C ] (hom-id C ∙[ C ] (hom-id C ∙[ C ] hom-id C))) , _ ⟫_) (sym (naturality (t ⟨ ob F e , f ∙[ E ] γ ⟩') (hom-id C) (trans (ctx-id (F*-ctx F (𝕪 (ob F e)))) (hom-idˡ D)))))
                   (trans (sym (ty-comp T))
                   (trans (ty-cong T (hom-idˡ C))
                          (trans (ty-comp T) (trans (ty-comp T) (trans (ty-comp T) (ty-comp T)))))))

-- strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (naturality (to (comp-eq-lock {G = G} {F} Γ))) (cong (func (to (comp-eq-lock {G = G} {F} Γ))) (trans (ctx-id (F*-ctx F (F*-ctx G Γ))) (sym (eq (F*-subst-𝝶 F {F*-ctx G (𝕪 e₂)} {F*-ctx G Γ} {𝝶 G {Γ} {e₂} γ₂} {ob F e} {f ∙[ E ] γ}) (hom-id D)))))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (naturality (to (comp-eq-lock {G = G} {F} Γ))) (cong (func (to (comp-eq-lock {G = G} {F} Γ))) (trans (naturality (F*-subst F (𝝶 G  {Γ} {e₂} γ₂))) (cong (func (F*-subst F (𝝶 G {Γ} {e₂} γ₂))) (trans (ctx-id (F*-ctx F (F*-ctx G (𝕪 e₂)))) (ctx-id (F*-ctx G (𝕪 e₂)))))))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym (eq (⊚-assoc {C} {F*-ctx (G ∘ᶠ F) (𝕪 e₂)} {F*-ctx F (F*-ctx G (𝕪 e₂))} {F*-ctx F (F*-ctx G Γ)} {Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩} {to (comp-eq-lock Γ)} {F*-subst F (𝝶 G γ₂)} {from (comp-eq-lock (𝕪 e₂))}) (f ∙[ E ] γ)))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym refl)) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (trans (ctx-comp Γ) (cong (Γ ⟪ γ ⟫_) eγ))))))
eq (isoˡ (comp-eq-mod-tyʳ {D} {E} {C} {G} {F} {Γ} T)) {e} {γ} t = 
  tm-≅-to-≡ (record { eq = λ {c} g → 
    trans (sym (ty-comp T)) 
    (trans (sym (ty-comp T)) 
    (trans (cong (λ s → T ⟪ hom-id C ∙[ C ] (hom-id C ∙[ C ] hom-id C) , strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (naturality (to (comp-eq-lock {G = G} {F} Γ))) (cong (func (to (comp-eq-lock {G = G} {F} Γ))) (trans (naturality (F*-subst F (𝝶 G {Γ} {e} γ))) (cong (func (F*-subst F (𝝶 G {Γ} {e} γ))) (trans (ctx-id (F*-ctx F (F*-ctx G (𝕪 e)))) (ctx-id (F*-ctx G (𝕪 e)))))))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym (eq (⊚-assoc {C} {F*-ctx (G ∘ᶠ F) (𝕪 e)} {F*-ctx F (F*-ctx G (𝕪 e))} {F*-ctx F (F*-ctx G Γ)} {Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩} {to (comp-eq-lock Γ)} {F*-subst F (𝝶 G γ)} {from (comp-eq-lock (𝕪 e))}) g))) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym refl))) ⟫ (s ⟨ c , hom-id D ⟩')) (eq (isoʳ (ty-lift-mod-natural F {F*-ctx G (𝕪 e)} {F*-ctx G Γ} (𝝶 G {Γ} γ))) ((ι[ ty-subst-comp T (to (comp-eq-lock Γ)) (F*-subst F (𝝶 G γ)) ] (ι[ ty-subst-cong-subst (record { eq = λ _ → refl }) T ] (ι[ ≅ᵗʸ-sym (ty-subst-comp T (𝝶 (G ∘ᶠ F) γ) (to (comp-eq-lock (𝕪 e)))) ] (t [ to (comp-eq-lock (𝕪 e)) ]')))) [ 𝝶 F g ]'))) 
    (trans (sym (ty-comp T)) 
    (trans (ty-cong T ((trans (hom-idˡ C) (trans (hom-idˡ C) (hom-idˡ C))))) 
           (naturality t (hom-id C) (trans (ctx-id (F*-ctx (G ∘ᶠ F) (𝕪 e))) (trans (cong (category-composition E g) (id-law G)) (hom-idʳ E)))))))) })
eq (isoʳ (comp-eq-mod-tyʳ {D} {E} {C} {G} {F} {Γ} T)) {e} {γ} t = 
  tm-≅-to-≡ (record { eq = λ {d} g → 
  tm-≅-to-≡ (record { eq = λ {c} h → 
    trans (sym (trans (ty-comp T) (trans (ty-comp T) (trans (ty-comp T) (trans (ty-comp T)  (ty-comp T)))))) 
    (trans (cong (T ⟪ hom-id C ∙[ C ] (hom-id C ∙[ C ] (hom-id C ∙[ C ] (hom-id C ∙[ C ] (hom-id C ∙[ C ] hom-id C)))) , strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (naturality (to (comp-eq-lock {G = G} {F} Γ))) (cong (func (to (comp-eq-lock {G = G} {F} Γ))) (trans (ctx-id (F*-ctx F (F*-ctx G Γ))) (sym (eq (F*-subst-𝝶 F {F*-ctx G (𝕪 e)} {F*-ctx G Γ} {𝝶 G γ}) (hom-id D)))))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (naturality (to (comp-eq-lock {G = G} {F} Γ))) (cong (func (to (comp-eq-lock {G = G} {F} Γ))) (trans (naturality (F*-subst F (𝝶 G {Γ} γ))) (cong (func (F*-subst F (𝝶 G {Γ} γ))) (trans (ctx-id (F*-ctx F (F*-ctx G (𝕪 e)))) (ctx-id (F*-ctx G (𝕪 e)))))))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym (eq (⊚-assoc {C} {F*-ctx (G ∘ᶠ F) (𝕪 e)} {F*-ctx F (F*-ctx G (𝕪 e))} {F*-ctx F (F*-ctx G Γ)} {Γ ,lock⟨ fun-to-mod (G ∘ᶠ F) ⟩} {to (comp-eq-lock Γ)} {F*-subst F (𝝶 G γ)} {from (comp-eq-lock (𝕪 e))}) ((E ∙ g) (hom G h))))) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym refl)) (strong-ctx-comp (F*-ctx (G ∘ᶠ F) Γ) (trans (ctx-id (F*-ctx (G ∘ᶠ F) Γ)) (sym refl)) (trans (naturality (to (comp-eq-lock {G = G} {F} Γ))) (cong (func (to (comp-eq-lock {G = G} {F} Γ))) (trans (ctx-id (F*-ctx F (F*-ctx G Γ))) (eq (F*-subst-𝝶 F {F*-ctx G (𝕪 e)} {F*-ctx G Γ} {𝝶 G {Γ} γ} {d} {g}) h)))))))) ⟫_) (cong (_⟨ c , hom-id D ⟩') (sym (naturality t h refl)))) 
    (trans (sym (ty-comp T)) 
    (trans (ty-cong T (trans (hom-idˡ C) (trans (hom-idˡ C) (trans (hom-idˡ C) (trans (hom-idˡ C) (trans (hom-idˡ C) (hom-idˡ C))))))) 
          (naturality (t ⟨ d , g ⟩') (hom-id C) (trans (ctx-id (F*-ctx F (𝕪 d))) (hom-idʳ D)))))) }) })

fun-to-mod-comp : {G : Functor D E} {F : Functor C D} →
                       fun-to-mod (G ∘ᶠ F) ≅ᵐ fun-to-mod G ⓜ fun-to-mod F
eq-lock fun-to-mod-comp = comp-eq-lock
eq-lock-natural-to fun-to-mod-comp = comp-eq-lock-natural-to
eq-mod-tyʳ fun-to-mod-comp = comp-eq-mod-tyʳ


--------------------------------------------------
-- `fun-to-mod` respects isomorphic functors.

NatTransf-to-CtxNatTransf : {F G : Functor C D} → NatTransf F G → CtxNatTransf (F* G) (F* F)
func (transf-op (NatTransf-to-CtxNatTransf η) Γ) {c} = Γ ⟪ transf-op η c ⟫_
naturality (transf-op (NatTransf-to-CtxNatTransf η) Γ) {δ = δ} = trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ δ) (sym (naturality η))) (ctx-comp Γ))
eq (naturality (NatTransf-to-CtxNatTransf η) σ) _ = naturality σ

cong-eq-lock : {F G : Functor C D} → F ≅ᶠ G → 
               (Γ : Ctx D) → Γ ,lock⟨ fun-to-mod F ⟩ ≅ᶜ Γ ,lock⟨ fun-to-mod G ⟩
from (cong-eq-lock F=G Γ) = transf-op (NatTransf-to-CtxNatTransf (to F=G)) Γ
to (cong-eq-lock F=G Γ) = transf-op (NatTransf-to-CtxNatTransf (from F=G)) Γ
eq (isoˡ (cong-eq-lock F=G Γ)) γ = trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γ) (isoˡ F=G)) (ctx-id Γ))
eq (isoʳ (cong-eq-lock F=G Γ)) γ = trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γ) (isoʳ F=G)) (ctx-id Γ))

cong-eq-lock-natural-to : {F G : Functor C D} → (F=G : F ≅ᶠ G) → 
                          {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) →
                          to (cong-eq-lock F=G Γ) ⊚ lock-fmap (fun-to-mod G) σ 
                            ≅ˢ 
                          lock-fmap (fun-to-mod F) σ ⊚ to (cong-eq-lock F=G Δ)
eq (cong-eq-lock-natural-to _ σ) _ = naturality σ
 
helper : {F G : Functor C D} (F=G : F ≅ᶠ G) {Γ : Ctx D} {d : Ob D} {γ : Γ ⟨ d ⟩} →
         𝝶 F γ ≅ˢ to (cong-eq-lock F=G Γ) ⊚ 𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d))
eq (helper {D = D} F=G {Γ} {γ = γ}) g = trans (cong (Γ ⟪_⟫ γ) (trans (sym (hom-idʳ D)) (trans (cong (category-composition D g) (sym (isoˡ F=G))) (sym (∙assoc D))))) (ctx-comp Γ)

cong-eq-mod-tyʳ : {F G : Functor C D} → (F=G : F ≅ᶠ G) → 
                  {Γ : Ctx D} (T : Ty (Γ ,lock⟨ fun-to-mod F ⟩)) → 
                  ⟨ fun-to-mod F ∣ T ⟩ ≅ᵗʸ ⟨ fun-to-mod G ∣ T [ to (cong-eq-lock F=G Γ) ] ⟩
func (from (cong-eq-mod-tyʳ {C} {D} {F} {G} F=G {Γ} T)) {d} {γ} t = 
  ι[ ≅ᵗʸ-sym (ty-subst-id (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ])) ]
    ι[ ≅ᵗʸ-sym (ty-subst-cong-subst {Δ = 𝕪 d ,lock⟨ fun-to-mod G ⟩} {F*-ctx G (𝕪 d)} {from (cong-eq-lock F=G (𝕪 d)) ⊚ to (cong-eq-lock F=G (𝕪 d))} {id-subst (F*-ctx G (𝕪 d))} (isoʳ (cong-eq-lock F=G (𝕪 d))) (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ])) ]
      ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]) (from (cong-eq-lock F=G (𝕪 d))) (to (cong-eq-lock F=G (𝕪 d)))) ] 
        ((ι[ ty-subst-cong-ty (from (cong-eq-lock F=G (𝕪 d))) (ty-subst-comp T (to (cong-eq-lock F=G Γ)) (𝝶 G {Γ} {d} γ)) ]
          ι[ ty-subst-comp T (to (cong-eq-lock F=G Γ) ⊚ 𝝶 G γ) (from (cong-eq-lock F=G (𝕪 d))) ]
            ι[ ty-subst-cong-subst {Δ = F*-ctx F (𝕪 d)} {F*-ctx F Γ} {to (cong-eq-lock F=G Γ) ⊚ 𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d))} {𝝶 F {Γ} {d} γ} (≅ˢ-sym (helper F=G)) T ] t) [ to (cong-eq-lock F=G (𝕪 d)) ]')
  {- ≅ᵗᵐ ι[ ≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-id (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]))) 
           (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-cong-subst (isoʳ (cong-eq-lock F=G (𝕪 d))) (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]))) 
                      (≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]) (from (cong-eq-lock F=G (𝕪 d))) (to (cong-eq-lock F=G (𝕪 d)))))) ]
         ((ι[ ty-helper F=G T ] t) [ to (cong-eq-lock F=G (𝕪 d)) ]')

    ---------------------
    F*-ctx F (𝕪 d) ⊢ t : T [ 𝝶 F γ ]
    ---------------------
    F*-ctx F (𝕪 d) ⊢ t ⟨ c , (f ∙[ D ] g) ∙[ D ] transf-op (from F=G) c ⟩' : T [ 𝝶 F γ ] ⟨ c , (f ∙[ D ] g) ∙[ D ] transf-op (from F=G) c ⟩'
                    = T ⟨ c , Γ ⟪ ((f ∙[ D ] g) ∙[ D ] transf-op (from F=G) c) ⟫ γ ⟩'
    ---------------------
    F*-ctx F (𝕪 d) ⊢ ι[ ty-helper F=G T ] t 
                        : T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ] [ from (cong-eq-lock F=G (𝕪 d)) ]
    ---------------------
    F*-ctx G (𝕪 d) ⊢ (ι[ ty-helper F=G T ] t) [ to (cong-eq-lock F=G (𝕪 d)) ]' 
                        : T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ] [ from (cong-eq-lock F=G (𝕪 d)) ] [ to (cong-eq-lock F=G (𝕪 d)) ]
    ---------------------
    F*-ctx G (𝕪 d) ⊢ ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]) _ _)
                          (≅ᵗʸ-trans (ty-subst-cong-subst (isoʳ (cong-eq-lock F=G (𝕪 d))))
                                      (ty-subst-id (T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]))) ] 
                          ((ι[ ty-helper F=G T ] t) 
                              [ to (cong-eq-lock F=G (𝕪 d)) ]') 
                        : T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]
  -}
naturality (from (cong-eq-mod-tyʳ {C} {D} {F} {G} F=G {Γ} T)) {d₁} {d₂} {γx = γ₁} {eγ} {t} = 
  tm-≅-to-≡ (record { eq = λ {c} g → 
    trans (sym (trans (ty-comp T) (ty-comp T))) 
   (trans (ty-cong T (sym (hom-idˡ C))) 
   (trans (ty-comp T) 
   (trans (cong (T ⟪ hom-id C ∙[ C ] (hom-id C ∙[ C ] hom-id C) , strong-ctx-comp (Γ ,lock⟨ fun-to-mod F ⟩) (trans (ctx-id (Γ ,lock⟨ fun-to-mod F ⟩)) (trans (ctx-comp Γ) (cong (Γ ⟪ func (to (cong-eq-lock F=G (𝕪 d₁))) g ⟫_) eγ))) (strong-ctx-comp (Γ ,lock⟨ fun-to-mod F ⟩) (trans (ctx-id (F*-ctx F Γ)) (sym (eq (≅ˢ-sym (helper F=G {Γ} {d₁} {γ₁})) (func (to (cong-eq-lock F=G (𝕪 d₁))) g)))) (trans (naturality (to (cong-eq-lock F=G Γ))) (cong (func (to (cong-eq-lock F=G Γ))) (trans (naturality (𝝶 G {Γ} {d₁} γ₁)) (cong (func (𝝶 G {Γ} {d₁} γ₁)) (trans (ctx-id (F*-ctx G (𝕪 d₁))) (eq (isoʳ (cong-eq-lock F=G (𝕪 d₁))) g))))))) ⟫_) (naturality t (hom-id C) (trans (ctx-id (F*-ctx F (𝕪 d₂))) (∙assoc D)))) 
   (trans (ty-comp T) (ty-comp T))))) })
func (to (cong-eq-mod-tyʳ {C} {D} {F} {G} F=G {Γ} T)) {d} {γ} t = 
  ι[ ty-subst-cong-subst {Δ = F*-ctx F (𝕪 d)} {F*-ctx F Γ} {𝝶 F γ} {to (cong-eq-lock F=G Γ) ⊚ 𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d))} (helper F=G) T ] 
    ι[ ty-subst-cong-subst {Δ = F*-ctx F (𝕪 d)} {Γ ,lock⟨ fun-to-mod F ⟩} {to (cong-eq-lock F=G Γ) ⊚ 𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d))} {to (cong-eq-lock F=G Γ) ⊚ (𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d)))} ⊚-assoc T ] 
      ι[ ≅ᵗʸ-sym (ty-subst-comp T (to (cong-eq-lock F=G Γ)) (𝝶 G {Γ} {d} γ ⊚ from (cong-eq-lock F=G (𝕪 d)))) ] 
        ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ]) (𝝶 G {Γ} {d} γ) (from (cong-eq-lock F=G (𝕪 d)))) ] 
          (t [ from (cong-eq-lock F=G (𝕪 d)) ]')
    {-
      F*-ctx G (𝕪 d) ⊢ t : T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ]
      --------------------- 
      F*-ctx F (𝕪 d) ⊢ t [ from (cong-eq-lock F=G (𝕪 d)) ]' : T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ] [ from (cong-eq-lock F=G (𝕪 d)) ]
      ---------------------
      F*-ctx F (𝕪 d) ⊢ ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ]) (𝝶 G γ) (from (cong-eq-lock F=G (𝕪 d)))) ] (t [ from (cong-eq-lock F=G (𝕪 d)) ]') : T [ to (cong-eq-lock F=G Γ) ] [ 𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d)) ]
      ---------------------
      F*-ctx F (𝕪 d) ⊢ ι[ ≅ᵗʸ-sym (ty-subst-comp T (to (cong-eq-lock F=G Γ)) (𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d)))) ] ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ]) (𝝶 G γ) (from (cong-eq-lock F=G (𝕪 d)))) ] (t [ from (cong-eq-lock F=G (𝕪 d)) ]') : T [ to (cong-eq-lock F=G Γ) ⊚ (𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d))) ]
      ---------------------
      F*-ctx F (𝕪 d) ⊢ ι[ ⊚-assoc ] ι[ ≅ᵗʸ-sym (ty-subst-comp T (to (cong-eq-lock F=G Γ)) (𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d)))) ] ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ]) (𝝶 G γ) (from (cong-eq-lock F=G (𝕪 d)))) ] (t [ from (cong-eq-lock F=G (𝕪 d)) ]') : T [ to (cong-eq-lock F=G Γ) ⊚ 𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d)) ]
      ---------------------
      F*-ctx F (𝕪 d) ⊢ ι[ ty-subst-cong-subst (helper F=G) T ] ι[ ⊚-assoc ] ι[ ≅ᵗʸ-sym (ty-subst-comp T (to (cong-eq-lock F=G Γ)) (𝝶 G γ ⊚ from (cong-eq-lock F=G (𝕪 d)))) ] ι[ ≅ᵗʸ-sym (ty-subst-comp (T [ to (cong-eq-lock F=G Γ) ]) (𝝶 G γ) (from (cong-eq-lock F=G (𝕪 d)))) ] (t [ from (cong-eq-lock F=G (𝕪 d)) ]') : T [ 𝝶 F γ ] 
    -}
naturality (to (cong-eq-mod-tyʳ {C} {D} {F} {G} F=G {Γ} T)) {y = d₂} {f} {γ₂} {eγ = eγ} {t} = 
  tm-≅-to-≡ (record { eq = λ {c} g → 
    trans (sym (trans (ty-comp T) (ty-comp T)))
    (trans (cong (T ⟪ hom-id C ∙[ C ] (hom-id C ∙[ C ] hom-id C) , strong-ctx-comp (Γ ,lock⟨ fun-to-mod F ⟩) (trans (ctx-id (Γ ,lock⟨ fun-to-mod F ⟩)) (sym (eq (⊚-assoc {Γ₁ = F*-ctx F (𝕪 d₂)} {F*-ctx G (𝕪 d₂)} {Γ ,lock⟨ fun-to-mod G ⟩} {Γ ,lock⟨ fun-to-mod F ⟩} {to (cong-eq-lock F=G Γ)} {𝝶 G γ₂} {from (cong-eq-lock F=G (𝕪 d₂))}) (f ∙[ D ] g)))) (strong-ctx-comp (Γ ,lock⟨ fun-to-mod F ⟩) (trans (ctx-id (F*-ctx F Γ)) (sym (eq (helper F=G {Γ} {d₂} {γ₂}) (f ∙[ D ] g)))) (trans (ctx-id (Γ ,lock⟨ fun-to-mod F ⟩)) (trans (ctx-comp Γ) (cong (Γ ⟪ g ⟫_) eγ)))) ⟫_) (sym (naturality t (hom-id C) (trans (ctx-id (F*-ctx G (𝕪 d₂))) (sym (∙assoc D))))))
    (trans (sym (ty-comp T))
    (trans (ty-cong T (hom-idˡ C))
           (trans (ty-comp T) (ty-comp T))))) })
eq (isoˡ (cong-eq-mod-tyʳ {C} {F = F} F=G T)) {d} t = 
  tm-≅-to-≡ (record { eq = λ {c} g → trans (sym (trans (ty-comp T) (trans (ty-comp T) (ty-comp T)))) (trans (ty-cong T ((trans (hom-idˡ C) (trans (hom-idˡ C) (hom-idˡ C))))) (naturality t (hom-id C) (trans (ctx-id (F*-ctx F (𝕪 d))) (eq (isoˡ (cong-eq-lock F=G (𝕪 d))) g)))) })
eq (isoʳ (cong-eq-mod-tyʳ {C} {G = G} F=G T)) {d} t = 
  tm-≅-to-≡ (record { eq = λ {c} g → trans (sym (trans (ty-comp T) (trans (ty-comp T) (ty-comp T)))) (trans (ty-cong T ((trans (hom-idˡ C) (trans (hom-idˡ C) (hom-idˡ C))))) (naturality t (hom-id C) (trans (ctx-id (F*-ctx G (𝕪 d))) (eq (isoʳ (cong-eq-lock F=G (𝕪 d))) g)))) })

fun-to-mod-cong : {F G : Functor C D} → F ≅ᶠ G → fun-to-mod F ≅ᵐ fun-to-mod G
eq-lock (fun-to-mod-cong F=G) = cong-eq-lock F=G
eq-lock-natural-to (fun-to-mod-cong F=G) = cong-eq-lock-natural-to F=G
eq-mod-tyʳ (fun-to-mod-cong F=G) = cong-eq-mod-tyʳ F=G


--------------------------------------------------
-- A natural transformation between functors between 
--   two base categories can be lifted to a two cell

NatTransf-to-TwoCell : {F G : Functor C D} → NatTransf F G → TwoCell (fun-to-mod F) (fun-to-mod G)
transf (NatTransf-to-TwoCell η) = NatTransf-to-CtxNatTransf η
