--------------------------------------------------
-- todo: Modalities between ★ ⊗ V and ω ⊗ V that does not do anything to V
--------------------------------------------------
open import Model.BaseCategory

module Applications.ClockedTypeTheory.Model.Temp (V : BaseCategory) where

open import Data.Nat
open import Data.Nat.Properties
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injectiveʳ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Functor
open import Model.Modality
open import Model.CwF-Structure
open import Model.CwF-Structure.LiftingFunctors.Modality
open import Model.Type.Function

open BaseCategory

private
  ω×V : BaseCategory
  ω×V = ω ⊗ V

  ★×V : BaseCategory
  ★×V = ★ ⊗ V

  variable
    m n : Ob ω
    x y : Ob V

ω-suc×id : Functor ω×V ω×V
ω-suc×id = ω-suc ⊗ᶠ id-functor {V}

𝒵×id : Functor ω×V ★×V
𝒵×id = 𝒵 ⊗ᶠ id-functor {V} 

𝒬×id : Functor ★×V ω×V
𝒬×id = 𝒬 ⊗ᶠ id-functor {V}


--------------------------------------------------
-- The `later` modality and its interaction with the unit modality

later : Modality ω×V ω×V
later = fun-to-mod ω-suc×id

◄ : Ctx ω×V → Ctx ω×V
◄ = lock later

𝝶-later : {Γ : Ctx ω×V} {d : Ob ω×V} → Γ ⟨ d ⟩ → ◄ (𝕪 d) ⇒ ◄ Γ
𝝶-later = 𝝶 ω-suc×id

ctx-m≤1+nˡ : (Γ : Ctx ω×V) {m≤n : m ≤ n} {g : Hom V x y} {γ : Γ ⟨ [ suc n , y ] ⟩} → 
             Γ ⟪ [ m≤n , g ] ⟫ (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ γ) 
               ≡ 
             Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ (Γ ⟪ [ s≤s m≤n , g ] ⟫ γ)
ctx-m≤1+nˡ Γ {γ = γ} = trans (sym (ctx-comp Γ)) 
                      (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ])) 
                      (trans (sym (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , hom-idʳ V ]))) 
                             (ctx-comp Γ)))

from-earlier : (Γ : Ctx ω×V) → ◄ Γ ⇒ Γ
func (from-earlier Γ) {[ n , _ ]} = Γ ⟪ [ n≤1+n n , hom-id V ] ⟫_
naturality (from-earlier Γ) = ctx-m≤1+nˡ Γ

module _ {Γ : Ctx ω×V} where
  -- Shorthands
  ▻ : Ty (◄ Γ) → Ty Γ
  ▻ = ⟨ later ∣_⟩

  ▻' : Ty Γ → Ty Γ
  ▻' T = ▻ (T [ from-earlier Γ ])

  next : {T : Ty (◄ Γ)} → Tm (◄ Γ) T → Tm Γ (▻ T)
  next = mod-intro later

  prev : {T : Ty (◄ Γ)} → Tm Γ (▻ T) → Tm (◄ Γ) T 
  prev = mod-elim later
  
  prev' : {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (T [ from-earlier Γ ])
  prev' t = t [ from-earlier Γ ]'

  next' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻' T)
  next' t = next (prev' t)

  -- Helpers for defining the `löb` primitive
  ◄-cancel : ◄ (𝕪 [ suc n , x ]) ≅ᶜ 𝕪 [ n , x ]
  func (from ◄-cancel) [ m+1≤n+1 , g ] = [ ≤-pred m+1≤n+1 , g ]
  naturality (from ◄-cancel) = ×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]
  func (to ◄-cancel) [ m≤n , g ] = [ s≤s m≤n , g ]
  naturality (to ◄-cancel) = ×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]
  eq (isoˡ ◄-cancel) [ m+1≤n+1 , g ] = ×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]
  eq (isoʳ ◄-cancel) [ m≤n , g ] = ×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]

  ⇋ : {γ : Γ ⟨ [ suc n , x ] ⟩} {T : Ty Γ} → 
      T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ] [ to ◄-cancel ] ⟨ [ n , x ] , [ ≤-refl , hom-id V ] ⟩ →
      Tm (𝕪 [ n , x ]) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ] [ to ◄-cancel ])
  ⇋ {γ = γ} {T} t ⟨ _ , [ m≤n , _ ] ⟩' = T ⟪ [ m≤n , _ ] , trans (cong (Γ ⟪ [ m≤n , _ ] ⟫_) (trans (sym (ctx-comp Γ)) (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ])))) 
                                                          (trans (ctx-m≤1+nˡ Γ) (cong (Γ ⟪_⟫ (Γ ⟪ [ s≤s m≤n , _ ] ⟫ γ)) (×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]))) ⟫ t
  naturality (⇋ {T = T} _) _ eγ = trans (sym (ty-comp T)) (ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , ,-injectiveʳ eγ ]))

  ⇋⁻¹ : {γ : Γ ⟨ [ suc n , x ] ⟩} {T : Ty Γ} → 
        Tm (𝕪 [ n , x ]) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ] [ to ◄-cancel ]) →
        T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ] [ to ◄-cancel ] ⟨ [ n , x ] , [ ≤-refl , hom-id V ] ⟩
  ⇋⁻¹ {n} {x} t = t ⟨ [ n , x ] , [ ≤-refl , hom-id V ] ⟩'

  ⇋⁻¹⇋=id : {γ : Γ ⟨ [ suc n , x ] ⟩} {T : Ty Γ} → 
            (t : T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ] [ to ◄-cancel ] ⟨ [ n , x ] , [ ≤-refl , hom-id V ] ⟩) →
            ⇋⁻¹ {n} {x} {γ} {T} (⇋ t) ≡ t
  ⇋⁻¹⇋=id {T = T} _ = trans (ty-cong T refl) (ty-id T)

  ⇋⇋⁻¹=id : {γ : Γ ⟨ [ suc n , x ] ⟩} {T : Ty Γ} → 
            (t : Tm (𝕪 [ n , x ]) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ] [ to ◄-cancel ])) →
            ⇋ (⇋⁻¹ t) ≅ᵗᵐ t
  eq (⇋⇋⁻¹=id {n} {y} {γ} {T} t) {[ m , x ]} [ m≤n , x→y ] =
    begin
      T ⟪ [ m≤n , x→y ] , _ ⟫
        t ⟨ [ n , y ] , [ ≤-refl , hom-id V ] ⟩'
    ≡⟨ ty-cong T refl ⟩
      T ⟪ [ m≤n , x→y ] , _ ⟫
        t ⟨ [ n , y ] , [ ≤-refl , hom-id V ] ⟩'
    ≡⟨ naturality t [ m≤n , x→y ] (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩
      t ⟨ [ m , x ] , [ m≤n , x→y ] ⟩' ∎
    where open ≡-Reasoning

  null : ∀ {γ} {T : Ty Γ} → Tm (◄ (𝕪 [ zero , x ])) (T [ from-earlier Γ ] [ 𝝶-later γ ])
  null ⟨ [ zero , _ ] , () ⟩'
  null ⟨ [ suc n , _ ] , () ⟩'

  löb : (T : Ty Γ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
  löb T f = MkTm ((λ { [ n , x ] → tm n x } )) λ { {[ m , x ]} {[ n , y ]} [ m≤n , g ] eγ → nat m≤n g eγ }
    where
      tm : (n : Ob ω) (x : Ob V) → (γ : Γ ⟨ [ n , x ] ⟩) → T ⟨ [ n , x ] , γ ⟩
      tm zero x γ = f €⟨ [ zero , x ] , γ ⟩ null
      tm (suc n) x γ = f €⟨ [ suc n , x ] , γ ⟩ 
                      (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) _ _) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ])) (ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]))) ]
                      (ιc[ ◄-cancel ]' ⇋ (tm n x (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ (func (𝝶-later {Γ} γ) [ s≤s ≤-refl , hom-id V ])))))
                      -- 

      open ≡-Reasoning
      nat : {m n : Ob ω} {x y : Ob V} {γₙ : Γ ⟨ [ n , y ] ⟩} {γₘ : Γ ⟨ [ m , x ] ⟩} (m≤n : m ≤ n) (g : Hom V x y) (eγ : Γ ⟪ [ m≤n , g ] ⟫ γₙ ≡ γₘ) →
            T ⟪ [ m≤n , g ] , eγ ⟫ tm n y γₙ ≡ tm m x γₘ
      nat {zero} {zero} {γₙ = γₙ} {γₘ} z≤n _ eγ =
        begin
          T ⟪ [ z≤n , _ ] , eγ ⟫
            f €⟨ [ zero , _ ] , γₙ ⟩ null
        ≡⟨ €-natural f ⟩
          f €⟨ [ zero , _ ] , γₘ ⟩
            (▻' T ⟪ [ z≤n , _ ] , eγ ⟫ null)
        ≡⟨ cong (f €⟨ [ zero , _ ] , γₘ ⟩_) (tm-≅-to-≡ (record { eq = λ () })) ⟩
          f €⟨ [ zero , _ ] , γₘ ⟩ null ∎
      nat {zero} {suc n} {γₘ = γₘ} _ _ _ = trans (€-natural f) (cong (f €⟨ [ zero , _ ] , γₘ ⟩_) (tm-≅-to-≡ (record { eq = λ () })))
      nat {suc m} {suc n} {x} {y} {γₙ = γₙ} {γₘ} (s≤s m≤n) g eγ = trans (€-natural f) (cong (f €⟨ [ suc m , _ ] , γₘ ⟩_) (tm-≅-to-≡ iso))
        where
          iso : ▻' T ⟪ [ s≤s m≤n , g ] , eγ ⟫
                (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp ((T [ from-earlier Γ ]) [ 𝝶-later γₙ ]) (to ◄-cancel) (from ◄-cancel)) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) ((T [ from-earlier Γ ]) [ 𝝶-later γₙ ])) (ty-subst-id ((T [ from-earlier Γ ]) [ 𝝶-later γₙ ]))) ]
                (ιc[ ◄-cancel ]' ⇋ (tm n y (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ func (𝝶-later {Γ} γₙ) [ s≤s ≤-refl , hom-id V ]))))
                  ≅ᵗᵐ
                ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp ((T [ from-earlier Γ ]) [ 𝝶-later γₘ ]) (to ◄-cancel) (from ◄-cancel)) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) ((T [ from-earlier Γ ]) [ 𝝶-later γₘ ])) (ty-subst-id ((T [ from-earlier Γ ]) [ 𝝶-later γₘ ]))) ]
                (ιc[ ◄-cancel ]' ⇋ (tm m x (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ func (𝝶-later {Γ} γₘ) [ s≤s ≤-refl , hom-id V ])))
          eq iso {[ k , z ]} [ s≤s k≤m , z→x ] =
            begin
              T ⟪ [ ≤-refl , hom-id V ] , _ ⟫
                T ⟪ [ ≤-refl , hom-id V ] , _ ⟫
                  T ⟪ [ ≤-pred (≤-trans (s≤s k≤m) (s≤s m≤n)) , _ ] , _ ⟫ 
                    tm n y (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ func (𝝶-later {Γ} γₙ) [ s≤s ≤-refl , hom-id V ])
            ≡⟨ sym (ty-comp T) ⟩
              T ⟪ [ ≤-trans ≤-refl ≤-refl , hom-id V ∙[ V ] hom-id V ] , _ ⟫
                T ⟪ [ ≤-pred (≤-trans (s≤s k≤m) (s≤s m≤n)) , _ ] , _ ⟫ 
                  tm n y (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ func (𝝶-later {Γ} γₙ) [ s≤s ≤-refl , hom-id V ])
            ≡⟨ sym (ty-comp T) ⟩
              T ⟪ [ ≤-trans (≤-trans ≤-refl ≤-refl) (≤-pred (≤-trans (s≤s k≤m) (s≤s m≤n))) , (g ∙[ V ] z→x) ∙[ V ] (hom-id V ∙[ V ] hom-id V) ] , _ ⟫
                tm n y (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ func (𝝶-later {Γ} γₙ) [ s≤s ≤-refl , hom-id V ])
            ≡⟨ ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , trans (cong (category-composition V (g ∙[ V ] z→x)) (hom-idˡ V)) (∙assoc V) ]) ⟩
              T ⟪ [ ≤-trans (≤-trans ≤-refl k≤m) m≤n , g ∙[ V ] (z→x ∙[ V ] hom-id V) ] , _ ⟫
                tm n y (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ func (𝝶-later {Γ} γₙ) [ s≤s ≤-refl , hom-id V ])
            ≡⟨ ty-comp T ⟩
              T ⟪ [ ≤-trans ≤-refl k≤m , z→x ∙[ V ] hom-id V ] , _ ⟫
                T ⟪ [ m≤n , g ] , _ ⟫
                  tm n y (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ func (𝝶-later {Γ} γₙ) [ s≤s ≤-refl , hom-id V ])
            ≡⟨ cong (T ⟪ [ ≤-trans ≤-refl k≤m , z→x ∙[ V ] hom-id V ] , _ ⟫_) (nat m≤n g (trans (sym (ctx-comp Γ)) (trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γₙ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , trans (cong (category-composition V (hom-id V)) (hom-idˡ V)) (trans (hom-idᵒ V) (cong (category-composition V g) (sym (hom-idˡ V)))) ])) (trans (ctx-comp Γ) (trans (ctx-comp Γ) (cong (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫_ ∘ Γ ⟪ [ s≤s ≤-refl , hom-id V ] ⟫_) eγ))))))) ⟩
              T ⟪ [ ≤-trans ≤-refl k≤m , z→x ∙[ V ] hom-id V ] , _ ⟫
                tm m x (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ func (𝝶-later {Γ} γₘ) [ s≤s ≤-refl , hom-id V ])
            ≡⟨ ty-comp T ⟩
              T ⟪ [ ≤-refl , hom-id V ] , _ ⟫
                T ⟪ [ k≤m , z→x ] , _ ⟫
                  tm m x (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ func (𝝶-later {Γ} γₘ) [ s≤s ≤-refl , hom-id V ]) ∎

  löb' : (T : Ty Γ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
  löb' T f = löb T (lam (▻' T) f)

  löb[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻' T) (T [ π ]) → Tm Γ T
  löb[_∈▻'_]_ v = löb'

  löb-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) → app f (next' (löb T f)) ≅ᵗᵐ löb T f
  eq (löb-is-fixpoint {T} f) {[ zero , x ]} γ = cong (f €⟨ [ zero , x ] , γ ⟩_) (tm-≅-to-≡ (record { eq = λ () }))
  eq (löb-is-fixpoint {T} f) {[ suc n , x ]} γ = cong (f €⟨ [ suc n , x ] , γ ⟩_) (tm-≅-to-≡ iso)
    where
      open ≡-Reasoning
      iso : next' (löb T f) ⟨ [ suc n , x ] , γ ⟩'
              ≅ᵗᵐ 
            ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) _ _) 
                (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ])) 
                           (ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]))) ] 
            (ιc[ ◄-cancel ]' ⇋ ((löb T f) ⟨ [ n , x ] , Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ (Γ ⟪ [ s≤s ≤-refl , hom-id V ] ⟫ γ) ⟩'))
      eq iso {[ k , z ]} [ k+1≤n+1 , k→x ] =
        begin
          (löb T f) ⟨ [ k , z ] , Γ ⟪ [ n≤1+n k , hom-id V ] ⟫ (Γ ⟪ [ k+1≤n+1 , k→x ] ⟫ γ) ⟩'
        ≡⟨ sym (naturality (löb T f) [ ≤-trans ≤-refl (≤-pred k+1≤n+1) , k→x ∙[ V ] hom-id V ] (trans (sym (ctx-comp Γ)) (trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , trans (hom-idˡ V) (hom-idˡ V) ])) (ctx-comp Γ))))) ⟩
          T ⟪ [ ≤-trans ≤-refl (≤-pred k+1≤n+1) , k→x ∙[ V ] hom-id V ] , _ ⟫
            (löb T f) ⟨ [ n , x ] , Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ (Γ ⟪ [ s≤s ≤-refl , hom-id V ] ⟫ γ) ⟩'
        ≡⟨ ty-cong T refl ⟩
          T ⟪ [ ≤-trans ≤-refl (≤-pred k+1≤n+1) , k→x ∙[ V ] hom-id V ] , _ ⟫
            (löb T f) ⟨ [ n , x ] , Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ (Γ ⟪ [ s≤s ≤-refl , hom-id V ] ⟫ γ) ⟩'
        ≡⟨ ty-comp T ⟩
          T ⟪ [ ≤-refl , hom-id V ] , _ ⟫
            T ⟪ [ ≤-pred k+1≤n+1 , k→x ] , _ ⟫ 
              (löb T f) ⟨ [ n , x ] , Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ (Γ ⟪ [ s≤s ≤-refl , hom-id V ] ⟫ γ) ⟩' ∎

  -- fixme:
  -- fixpoint-unique : {T : Ty Γ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
  --                   app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
  -- eq (fixpoint-unique f _ _ t-fix s-fix) {[ zero , _ ]} γ = trans (sym (eq t-fix γ)) (trans (cong (f €⟨ [ zero , _ ] , γ ⟩_) (tm-≅-to-≡ (record { eq = λ () }))) (eq s-fix γ))
  -- eq (fixpoint-unique f t s t-fix s-fix) {[ suc n , x ]} γ = 
  --   begin
  --     t ⟨ [ suc n , x ] , γ ⟩'
  --   ≡˘⟨ eq t-fix γ ⟩
  --     f €⟨ [ suc n , x ] , γ ⟩ (t [ _ ]' [ _ ]')
  --   ≡⟨ cong (f €⟨ [ suc n , x ] , γ ⟩_) (tm-≅-to-≡ (record { eq = λ {_} h → eq (fixpoint-unique f t s t-fix s-fix) (func (from-earlier Γ) (func (𝝶-later {Γ} γ) h)) })) ⟩
  --     f €⟨ [ suc n , x ] , γ ⟩ (s [ _ ]' [ _ ]')
  --   ≡⟨ eq s-fix γ ⟩
  --     s ⟨ [ suc n , x ] , γ ⟩' ∎
  --   where open ≡-Reasoning
  
  -- 2ND ATTEMPT
  -- fixpoint-unique : {T : Ty Γ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
  --                   app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
  -- eq (fixpoint-unique f _ _ t-fix s-fix) {[ zero , _ ]} γ = trans (sym (eq t-fix γ)) (trans (cong (f €⟨ [ zero , _ ] , γ ⟩_) (tm-≅-to-≡ (record { eq = λ () }))) (eq s-fix γ))
  -- eq (fixpoint-unique {T} f t s t-fix s-fix) {[ suc n , x ]} γ = trans (sym (eq t-fix γ)) (trans (cong (f €⟨ [ suc n , x ] , γ ⟩_) step₇) (eq s-fix γ))
  --   where
  --     step₁ : ⇋⁻¹ (t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]')
  --               ≡
  --             ⇋⁻¹ (s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]')
  --     step₁ = eq (fixpoint-unique f t s t-fix s-fix) ((func (from-earlier Γ) (func (𝝶-later {Γ} γ) _)))
      
  --     step₂ : ⇋ {T = T} (⇋⁻¹ (t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'))
  --               ≡
  --             ⇋ (⇋⁻¹ (s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'))
  --     step₂ = cong ⇋ step₁

  --     step₃ : t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'
  --               ≡
  --             s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'
  --     step₃ = 
  --       begin
  --         t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'
  --       ≡˘⟨ tm-≅-to-≡ (⇋⇋⁻¹=id (t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]')) ⟩
  --         ⇋ (⇋⁻¹ (t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'))
  --       ≡⟨ step₂ ⟩
  --         ⇋ (⇋⁻¹ (s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'))
  --       ≡⟨ tm-≅-to-≡ ((⇋⇋⁻¹=id (s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]'))) ⟩
  --         s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]' ∎
  --       where open ≡-Reasoning

  --     step₄ : t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]' [ from ◄-cancel ]'
  --               ≡
  --             s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]' [ from ◄-cancel ]'
  --     step₄ = cong (_[ from ◄-cancel ]') step₃

  --     step₅ : {r : Tm Γ T} → r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' [ to ◄-cancel ]' [ from ◄-cancel ]' 
  --                              ≅ᵗᵐ 
  --                            ι[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --                            ι[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --                            ι[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --                            (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')
  --     step₅ {r} = ≅ᵗᵐ-trans (tm-subst-comp (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]') (to ◄-cancel) (from ◄-cancel))
  --                (≅ᵗᵐ-trans (ι-cong (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel)) (tm-subst-cong-subst (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]') (isoˡ ◄-cancel))) 
  --                           (ι-cong (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel)) (ι-cong (ty-subst-cong-subst (isoˡ ◄-cancel) ((T [ from-earlier Γ ]) [ 𝝶-later γ ])) (tm-subst-id (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')))))

  --     step₆ : {r : Tm Γ T} → ι⁻¹[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --                            ι⁻¹[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --                            ι⁻¹[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --                            ι[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --                            ι[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --                            ι[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --                            (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')
  --                              ≅ᵗᵐ
  --                            r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]'
  --     step₆ {r} = ≅ᵗᵐ-trans (ι⁻¹-cong (ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ])) (ι⁻¹-cong (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ])) (ι-symˡ (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel)) _))) 
  --                (≅ᵗᵐ-trans (ι⁻¹-cong (ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ])) (ι-symˡ (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ])) (ι[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ] (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')))) 
  --                           (ι-symˡ (ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ])) (r [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')))
      
  --     step₇ = 
  --       begin
  --         t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]'
  --       ≡˘⟨ tm-≅-to-≡ (step₆ {t}) ⟩
  --         ι⁻¹[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --         ι⁻¹[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --         ι⁻¹[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --         ι[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --         ι[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --         ι[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --         (t [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')
  --       -- ≡⟨ {!   !} ⟩
  --       -- ≡⟨ {!   !} ⟩
  --       -- ≡⟨ {!   !} ⟩
  --       -- ≡⟨ {!   !} ⟩
  --       -- ≡⟨ {!   !} ⟩
  --       ≡⟨ cong (ι⁻¹[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]_ ∘ ι⁻¹[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]_ ∘ ι⁻¹[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]_) (trans (sym (tm-≅-to-≡ (step₅ {t}))) (trans (step₄) (tm-≅-to-≡ (step₅ {s})))) ⟩
  --         ι⁻¹[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --         ι⁻¹[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --         ι⁻¹[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --         ι[ ty-subst-comp (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) (to ◄-cancel) (from ◄-cancel) ]
  --         ι[ ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶-later {Γ} γ ]) ]
  --         ι[ ty-subst-id (T [ from-earlier Γ ] [ 𝝶-later γ ]) ]
  --         (s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]')
  --       ≡⟨ tm-≅-to-≡ (step₆ {s}) ⟩
  --         s [ from-earlier Γ ]' [ 𝝶-later {Γ} γ ]' ∎
  --       where open ≡-Reasoning

  -- ▻ is an applicative functor
  _⟨$⟩_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T) → Tm Γ (▻ S)
  f ⟨$⟩ t = next (app f (prev t))

  _⊛_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
  f ⊛ t = prev f ⟨$⟩ t

from-earlier-naturalˡ : {Γ Δ : Ctx ω×V} (σ : Δ ⇒ Γ) → from-earlier Γ ⊚ lock-fmap later σ ≅ˢ σ ⊚ from-earlier Δ
eq (from-earlier-naturalˡ σ) _ = naturality σ

𝟙≤later : TwoCell 𝟙 later
transf-op (transf 𝟙≤later) = from-earlier
CtxNatTransf.naturality (transf 𝟙≤later) = from-earlier-naturalˡ


--------------------------------------------------
-- The `forever` modality and its interaction with the `later` modality

forever : Modality ω×V ★×V
forever = fun-to-mod 𝒵×id

𝝶-forever : {Γ : Ctx ★×V} {d : Ob ★×V} → Γ ⟨ d ⟩ → (𝕪 d) ,lock⟨ forever ⟩ ⇒ Γ ,lock⟨ forever ⟩
𝝶-forever = 𝝶 𝒵×id

constantly-ctx = lock forever

𝒵×id∘ω-suc×id=𝒵×id : 𝒵×id ∘ᶠ ω-suc×id ≅ᶠ 𝒵×id
𝒵×id∘ω-suc×id=𝒵×id = ⊗ᶠ-congʳ id-functor (𝒵∘functor=𝒵 ω-suc)

forever-later : forever ⓜ later ≅ᵐ forever
forever-later = ≅ᵐ-trans (≅ᵐ-sym fun-to-mod-comp) (fun-to-mod-cong 𝒵×id∘ω-suc×id=𝒵×id)

forever-later'-ty : {Γ : Ctx ★×V} (T : Ty (Γ ,lock⟨ forever ⟩)) → ⟨ forever ∣ ▻' T ⟩ ≅ᵗʸ ⟨ forever ∣ T ⟩
forever-later'-ty {Γ = Γ} T =
  begin
    ⟨ forever ∣ ▻' T ⟩
  ≅⟨ mod-cong forever (mod-cong later (ty-subst-cong-subst (record { eq = λ _ → refl }) T)) ⟩
    ⟨ forever ∣ ▻ (T [ from (eq-lock forever-later Γ) ]) ⟩
  ≅⟨ eq-mod-tyˡ forever-later T ⟩
    ⟨ forever ∣ T ⟩ ∎
  where open ≅ᵗʸ-Reasoning


--------------------------------------------------
-- The `constantly` modality and its interaction with other modalities

constantly : Modality ★×V ω×V
constantly = fun-to-mod 𝒬×id

𝝶-constantly : {Γ : Ctx ω×V} {d : Ob ω×V} → Γ ⟨ d ⟩ → (𝕪 d) ,lock⟨ constantly ⟩ ⇒ Γ ,lock⟨ constantly ⟩
𝝶-constantly = 𝝶 𝒬×id

now = lock constantly

𝒵×id∘𝒬×id=id : 𝒵×id ∘ᶠ 𝒬×id ≅ᶠ id-functor {★×V}
𝒵×id∘𝒬×id=id = transᶠ (⊗ᶠ-congʳ id-functor (transᶠ (𝒵∘functor=𝒵 𝒬) 𝒵-id)) ⊗ᶠ-id

forever-constantly : forever ⓜ constantly ≅ᵐ 𝟙
forever-constantly =
  begin
    forever ⓜ constantly
  ≅⟨ ≅ᵐ-sym fun-to-mod-comp ⟩
    fun-to-mod (𝒵×id ∘ᶠ 𝒬×id)
  ≅⟨ fun-to-mod-cong 𝒵×id∘𝒬×id=id ⟩
    fun-to-mod id-functor
  ≅⟨ fun-to-mod-id ⟩
    𝟙 ∎
  where open ≅ᵐ-Reasoning

now-constantly-ctx-intro : {T : ClosedTy ★×V} {{_ : IsClosedNatural T}} {Γ : Ctx ★×V} →
                           Tm Γ T → Tm ((Γ ,lock⟨ forever ⟩) ,lock⟨ constantly ⟩) T
now-constantly-ctx-intro {T} t = mod-elim constantly (mod-elim forever (ι[ eq-mod-closed forever-constantly T ] t))

to-constantly-now-ctx : (Γ : Ctx ω×V) → (Γ ⇒ (Γ ,lock⟨ constantly ⟩) ,lock⟨ forever ⟩)
func (to-constantly-now-ctx Γ) = Γ ⟪ [ z≤n , hom-id V ] ⟫_
naturality (to-constantly-now-ctx Γ) {δ = δ} = trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ δ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idᵒ V ])) (ctx-comp Γ))

to-constantly-now-ctx-natural : {Δ Γ : Ctx ω×V} (σ : Δ ⇒ Γ) →
    to-constantly-now-ctx Γ ⊚ σ ≅ˢ ctx-fmap (ctx-functor forever ⓕ ctx-functor constantly) σ ⊚ to-constantly-now-ctx Δ
eq (to-constantly-now-ctx-natural σ) δ = _⇒_.naturality σ

constantly∘forever≤𝟙 : TwoCell (constantly ⓜ forever) 𝟙
transf-op (transf constantly∘forever≤𝟙) = to-constantly-now-ctx
CtxNatTransf.naturality (transf constantly∘forever≤𝟙) = to-constantly-now-ctx-natural

from-constantly-forever-ty : {Γ : Ctx ω×V} {T : Ty ((Γ ,lock⟨ constantly ⟩) ,lock⟨ forever ⟩)} →
                             Tm Γ ⟨ constantly ∣ ⟨ forever ∣ T ⟩ ⟩ → Tm Γ (T [ to-constantly-now-ctx Γ ])
from-constantly-forever-ty {Γ = Γ} t = mod-elim forever (mod-elim constantly t) [ to-constantly-now-ctx Γ ]'
 