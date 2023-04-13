--------------------------------------------------
-- The now-constantly dependent adjunction
--------------------------------------------------
open import Model.BaseCategory

module Applications.CombiningFeatures.Model.Modalities.Constantly (V : BaseCategory) where

open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injectiveʳ)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Discrete

open BaseCategory

ω×V : BaseCategory
ω×V = ω ⊗ V

private
  variable
    Δ Γ Θ : Ctx ω×V


--------------------------------------------------
-- The context operation

{-
  Γ = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... @ ω×V
  ---------------------------------
  now Γ = ✲₀ @ V

  The context operator `_,lock⟨ constantly ⟩` of modality `constantly` 
  
-}
now : Ctx ω×V → Ctx V
now Γ ⟨ x ⟩ = Γ ⟨ [ 0 , x ] ⟩
now Γ ⟪ f ⟫ γ = Γ ⟪ [ z≤n {zero} , f ] ⟫ γ
ctx-id (now Γ) = ctx-id Γ
ctx-comp (now Γ) = ctx-comp Γ

{- 
  The action of `now` on the morphisms (i.e., context substitutions) of Psh(ω × V)
  @ ω × V
                Δ⟨✲₀⟩ ← Δ⟨✲₁⟩ ← Δ⟨✲₂⟩ ← Δ⟨✲₃⟩ ...
            σ :   ↓        ↓       ↓        ↓
                Γ⟨✲₀⟩ ← Γ⟨✲₁⟩ ← Γ⟨✲₂⟩ ← Γ⟨✲₃⟩ ...

                Δ⟨✲₀⟩
  now-subst σ :   ↓
                Γ⟨✲₀⟩
-}
now-subst : Δ ⇒ Γ → now Δ ⇒ now Γ
func (now-subst σ) = func σ
_⇒_.naturality (now-subst σ) = _⇒_.naturality σ

-- The action of `now` on the morphisms of Psh(ω × V) respects equivalence of substitutions `_≅ˢ_`.
now-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → now-subst σ ≅ˢ now-subst τ
eq (now-subst-cong σ=τ) δ = eq σ=τ δ

-- The action of `now` on the morphisms of Psh(ω × V) preserves the identity morphisms of Psh(ω × V).
now-subst-id : now-subst (id-subst Γ) ≅ˢ id-subst (now Γ)
eq now-subst-id _ = refl

-- The action of `now` on the morphisms of Psh(ω × V) commutes with substitution compositions (i.e., the composition operation of Psh(ω × V)).
now-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → now-subst (σ ⊚ τ) ≅ˢ now-subst σ ⊚ now-subst τ
eq (now-subst-⊚ σ τ) _ = refl

-- A proof that `now` is a functor
instance
  now-is-functor : IsCtxFunctor now
  ctx-map {{now-is-functor}} = now-subst
  ctx-map-cong {{now-is-functor}} = now-subst-cong
  ctx-map-id {{now-is-functor}} = now-subst-id
  ctx-map-⊚ {{now-is-functor}} = now-subst-⊚


--------------------------------------------------
-- The `constantly` modality and corresponding term formers

{-
  Γ = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... @ ω×V
  ---------------------------------
  now Γ = ✲₀ @ V
  now Γ ⊢ T = ✲₀ @ V
  ---------------------------------
  Γ ⊢ constantly-ty T = ✲₀ ← ✲₀ ← ✲₀ ... @ ω×V
       constantly-ty T ⟨ [ m , x ] , γ ⟩ 
                                with γ : Γ ⟨ [ m , x ] ⟩
  Type `constantly-ty T` at `⟨ [ m , x ] , γ ⟩` depends on the pullback of γ from Γ ⟨ [ m , x ] ⟩ to Γ ⟨ [ 0 , x ] ⟩.
-}
constantly-ty : Ty (now Γ) → Ty Γ
constantly-ty {Γ = Γ} T ⟨ [ m , x ] , γ ⟩ = T ⟨ x , Γ ⟪ [ z≤n , hom-id V ] ⟫ γ ⟩
_⟪_,_⟫_ (constantly-ty {Γ = Γ} T) [ m≤n , g ] {γy = γₙ} {γx = γₘ} eγ = T ⟪ g , proof ⟫_
  {-
    eγ : Γ ⟪ [ m≤n , g ] ⟫ γₙ ≡ γₘ

    proof : 
      Γ ⟪ [ z≤n {zero} , g ] ⟫ (Γ ⟪ [ z≤n {n} , hom-id V {y} ] ⟫ γₙ) ≡ Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γₘ
    
    `z≤n` refers to a term constructor for type `_≤_`
  -}
  where
    open ≡-Reasoning
    proof : Γ ⟪ [ z≤n {zero} , g ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γₙ) ≡ Γ ⟪ [ z≤n , hom-id V ] ⟫ γₘ
    proof =
      begin
        Γ ⟪ [ z≤n {zero} , g ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γₙ)
      ≡˘⟨ ctx-comp Γ ⟩
        Γ ⟪ [ ≤-trans (z≤n {zero}) (z≤n) , (_∙_) V (hom-id V) g ] ⟫ γₙ
      ≡⟨ cong (Γ ⟪_⟫ γₙ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩ 
        Γ ⟪ [ ≤-trans (z≤n) m≤n , g ] ⟫ γₙ
      ≡˘⟨ cong (Γ ⟪_⟫ γₙ) (×-≡,≡→≡ [ refl , hom-idʳ V ]) ⟩
        Γ ⟪ [ ≤-trans (z≤n) m≤n , (_∙_) V g (hom-id V) ] ⟫ γₙ
      ≡⟨ ctx-comp Γ ⟩
        Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ m≤n , g ] ⟫ γₙ)
      ≡⟨ cong (Γ ⟪ [ z≤n , hom-id V ] ⟫_) eγ ⟩
        Γ ⟪ [ z≤n , hom-id V ] ⟫ γₘ ∎
ty-cong (constantly-ty T) e = ty-cong T (,-injectiveʳ e)
ty-id (constantly-ty T) = strong-ty-id T
ty-comp (constantly-ty T) = strong-ty-comp T

module _ {T : Ty (now Γ)} where
  {-
    now Γ ⊢ t : ✲₀ @ V
    ----------------------------------------------
    Γ ⊢ constantly-ty t = ✲₀ ← ✲₀ ← ✲₀ ... @ ω×V

    The action of `constantly` on terms (i.e., the term constructor `mod-intro(_)`)
  -}  
  constantly-tm : Tm (now Γ) T → Tm Γ (constantly-ty T)
  constantly-tm t ⟨ [ m , x ] , γ ⟩' = t ⟨ x , Γ ⟪ [ z≤n {m} , hom-id V ] ⟫ γ ⟩'
  Tm.naturality (constantly-tm t) {γy = γₙ} {γx = γₘ} [ m≤n , g ] eγ = Tm.naturality t g proof
    where
      open ≡-Reasoning
      proof : Γ ⟪ [ z≤n {zero} , g ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γₙ) ≡ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γₘ)
      proof =
        begin
          Γ ⟪ [ z≤n {zero} , g ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γₙ)
        ≡˘⟨ ctx-comp Γ ⟩
          Γ ⟪ [ ≤-trans (z≤n {zero}) (z≤n) , (_∙_) V (hom-id V) g ] ⟫ γₙ
        ≡⟨ cong (Γ ⟪_⟫ γₙ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩ 
          Γ ⟪ [ ≤-trans (z≤n) m≤n , g ] ⟫ γₙ
        ≡˘⟨ cong (Γ ⟪_⟫ γₙ) (×-≡,≡→≡ [ refl , hom-idʳ V ]) ⟩
          Γ ⟪ [ ≤-trans (z≤n) m≤n , (_∙_) V g (hom-id V) ] ⟫ γₙ
        ≡⟨ ctx-comp Γ ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ m≤n , g ] ⟫ γₙ)
        ≡⟨ cong (Γ ⟪ [ z≤n , hom-id V ] ⟫_) eγ ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ γₘ ∎
    {-
      constantly-ty T ⟨ [ m , x ] , γm ⟩ ←--------------------------------------- constantly-ty T ⟨ [ n , y ] , γn ⟩
                                          constantly-ty T ⟪ [ m≤n , g ] , eγ ⟫_
      constantly-ty t ⟨ [ m , x ] , γm ⟩' ←-------------------------------------| constantly-ty t ⟨ [ n , y ] , γn ⟩'

      RHS : 
        T ⟪ g , `proof` ⟫ (t ⟨ y , Γ ⟪ [ z≤n {n} , hom-id V {y} ] ⟫ γn ⟩') ≡ t ⟨ x , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γx ⟩'
    -}

  {-
    Γ ⊢ constantly-ty T = ✲₀ ← ✲₀ ← ✲₀ ... @ ω×V
    Γ ⊢ t : ✲₀ ← ✲₀ ← ✲₀ ... @ ω×V
    ----------------------------------------------
    now Γ ⊢ unconstantly-tm t : ✲₀ @ V

    The inverse of the action of `constantly` on terms
  -}
  unconstantly-tm : Tm Γ (constantly-ty T) → Tm (now Γ) T
  unconstantly-tm t ⟨ x , γ ⟩' = ty-ctx-subst T (ctx-id (now Γ) {x} {γ}) (t ⟨ [ 0 , x ] , γ ⟩')
    {-
      t ⟨ [ 0 , x ] , γ ⟩' : constantly-ty T ⟨ [ 0 , x ] , γ ⟩ 
                                  = T ⟨ x , Γ ⟪ [ z≤n , hom-id V {x} ] ⟫ γ ⟩
                                  = T ⟨ x , now Γ ⟪ hom-id V {x} ⟫ γ ⟩

      γ                              : now Γ ⟨ x ⟩ = Γ ⟨ [ 0 , x ] ⟩
      Γ ⟪ [ z≤n , hom-id V {x} ] ⟫ γ : now Γ ⟨ x ⟩ = Γ ⟨ [ 0 , x ] ⟩

        unconstantly-tm t ⟨ x , γ ⟩' : T ⟨ x , γ ⟩ 
      = ty-ctx-subst {now Γ} T {δ = now Γ ⟪ hom-id V {x} ⟫ γ} {δ' = γ} (ctx-id (now Γ) {x} {γ} : δ ≡ δ') (t ⟨ [ 0 , x ] , γ ⟩')
      = T ⟪ hom-id V {x} , trans (ctx-id (now Γ) {x} {now Γ ⟪ hom-id V {x} ⟫ γ}) (ctx-id (now Γ) {x} {γ}) ⟫ (t ⟨ [ 0 , x ] , γ ⟩')

        trans (ctx-id (now Γ) {x} {now Γ ⟪ hom-id V {x} ⟫ γ}) (ctx-id (now Γ) {x} {γ})
      = now Γ ⟪ hom-id V {x} ⟫ (now Γ ⟪ hom-id V {x} ⟫ γ) ≡ now Γ ⟪ hom-id V {x} ⟫ γ ≡ γ
    -}
  Tm.naturality (unconstantly-tm t) {x} {y} {γy} {γx} g eγ = proof'
    {- 
      g : x → y   
      γy : now Γ ⟨ y ⟩ = Γ ⟨ [ 0 , y ] ⟩
      γx : now Γ ⟨ x ⟩ = Γ ⟨ [ 0 , x ] ⟩
      eγ : `now Γ ⟪ g ⟫ γy ≡ γx` = `Γ ⟪ [ z≤n , g ] ⟫ γy ≡ γx`

      RHS (what we literally want) : T ⟪ g , eγ ⟫ (unconstantly-tm t ⟨ y , γy ⟩') ≡ unconstantly-tm t ⟨ x , γx ⟩'
                T ⟨ x , γx ⟩ ←------------------------------------------------- T ⟨ y , γy ⟩
                                                  T ⟪ g , eγ ⟫_ 
      unconstantly-tm t ⟨ x , γx ⟩'  ←----------------------------------| unconstantly-tm t ⟨ y , γy ⟩'
    -}
    {- Tm.naturality t
      Tm.naturality t {γn} {γm} [ m≤n , g ] eγ 
        : constantly-ty T ⟪ [ m≤n , g ] , eγ ⟫ (t ⟨ [ n , y ] , γn ⟩') ≡ t ⟨ [ m , x ] , γm ⟩'

      In our case: 
          Tm.naturality t {γy} {γx} [ z≤n , g ] eγ 
        : constantly-ty T ⟪ [ z≤n , g ] , eγ ⟫ (t ⟨ [ 0 , y ] , γy ⟩') ≡ t ⟨ [ 0 , x ] , γx ⟩'
        = T ⟪ g , proof ⟫ (t ⟨ [ 0 , y ] , γy ⟩') ≡ t ⟨ [ 0 , x ] , γx ⟩'
      with 
        - proof : now Γ ⟪ g ⟫ (now Γ ⟪ hom-id V ⟫ γy) ≡ now Γ ⟪ hom-id V ⟫ γx
        - t ⟨ [ 0 , y ] , γy ⟩' : constantly-ty T ⟨ [ 0 , y ] , γy ⟩' = T ⟨ y , Γ ⟪ [ z≤n , hom-id {y} ] ⟫ γy ⟩
        - t ⟨ [ 0 , x ] , γx ⟩' : constantly-ty T ⟨ [ 0 , x ] , γx ⟩' = T ⟨ x , Γ ⟪ [ z≤n , hom-id {x} ] ⟫ γx ⟩

      constantly-ty T ⟨ [ 0 , x ] , γx ⟩ ←-------------------------------------------- constantly-ty T ⟨ [ 0 , y ] , γy ⟩
                                            constantly-ty T ⟪ [ z≤n , g ] , eγ ⟫_
                t ⟨ [ 0 , x ] , γx ⟩'  ←-------------------------------------------------| t ⟨ [ 0 , y ] , γy ⟩'
    -}
    where
      open ≡-Reasoning
      proof : now Γ ⟪ g ⟫ (now Γ ⟪ hom-id V ⟫ γy) ≡ now Γ ⟪ hom-id V ⟫ γx
      proof =
        begin
          Γ ⟪ [ z≤n {zero} , g ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γy)
        ≡˘⟨ ctx-comp Γ ⟩
          Γ ⟪ [ ≤-trans (z≤n {zero}) (z≤n) , (_∙_) V (hom-id V) g ] ⟫ γy
        ≡⟨ cong (Γ ⟪_⟫ γy) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩ 
          Γ ⟪ [ ≤-trans z≤n z≤n , g ] ⟫ γy
        ≡˘⟨ cong (Γ ⟪_⟫ γy) (×-≡,≡→≡ [ refl , hom-idʳ V ]) ⟩
          Γ ⟪ [ ≤-trans z≤n z≤n , (_∙_) V g (hom-id V) ] ⟫ γy
        ≡⟨ ctx-comp Γ ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ z≤n , g ] ⟫ γy)
        ≡⟨ cong (Γ ⟪ [ z≤n , hom-id V ] ⟫_) eγ ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ γx ∎

      proof' : T ⟪ g , eγ ⟫ (unconstantly-tm t ⟨ y , γy ⟩') ≡ unconstantly-tm t ⟨ x , γx ⟩'
      proof' = 
        begin
          T ⟪ g , eγ ⟫ (unconstantly-tm t ⟨ y , γy ⟩')
        ≡⟨⟩
          T ⟪ g , eγ ⟫ (T ⟪ hom-id V , trans (ctx-id (now Γ)) (ctx-id (now Γ)) ⟫ (t ⟨ [ 0 , y ] , γy ⟩'))
        ≡˘⟨ ty-comp T ⟩
          T ⟪ (_∙_) V (hom-id V) g , strong-ctx-comp (now Γ) (trans (ctx-id (now Γ)) (ctx-id (now Γ))) eγ ⟫ (t ⟨ [ 0 , y ] , γy ⟩')
        ≡⟨ ty-cong T (hom-idˡ V) ⟩
          T ⟪ g , trans proof (ctx-id (now Γ)) ⟫ (t ⟨ [ 0 , y ] , γy ⟩')
        ≡˘⟨ ty-cong T (hom-idʳ V) ⟩ 
          T ⟪ (_∙_) V g (hom-id V) , strong-ctx-comp (now Γ) proof (trans (ctx-id (now Γ)) (ctx-id (now Γ))) ⟫ (t ⟨ [ 0 , y ] , γy ⟩')
        ≡⟨ ty-comp T ⟩
          T ⟪ hom-id V {x} , trans (ctx-id (now Γ)) (ctx-id (now Γ)) ⟫ (T ⟪ g , proof ⟫ (t ⟨ [ 0 , y ] , γy ⟩')) 
        ≡⟨⟩ 
          ty-ctx-subst T (ctx-id (now Γ)) (T ⟪ g , proof ⟫ (t ⟨ [ 0 , y ] , γy ⟩'))
        ≡⟨ cong (ty-ctx-subst T (ctx-id (now Γ))) (Tm.naturality t [ z≤n , g ] eγ) ⟩
          ty-ctx-subst T (ctx-id (now Γ)) (t ⟨ [ 0 , x ] , γx ⟩')
        ≡⟨⟩
          unconstantly-tm t ⟨ x , γx ⟩' ∎

  -- η rule
  constantly-ty-η : (t : Tm Γ (constantly-ty T)) → constantly-tm (unconstantly-tm t) ≅ᵗᵐ t
  eq (constantly-ty-η t) {[ m , x ]} γ = proof''
    {- USE OF Tm.naturality : 
      Tm.naturality t {x = [ 0 , x ]} {y = [ m , x ]} 
                      {γy = γ} 
                      {γx = Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ} 
                      [ z≤n {m} , hom-id V {x} ] 
                      (eγ = refl : Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ ≡ Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ) 
      :  
        constantly-ty T ⟪ [ z≤n {m} , hom-id V {x} ] , refl ⟫ (t ⟨ [ m , x ] , γ ⟩') 
      ≡ t ⟨ [ 0 , x ] , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ ⟩' 
      of type 
        constantly-ty T ⟨ [ 0 , x ] , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ ⟩
      = T ⟨ x , Γ ⟪ [ 0≤0 , hom-id V {x} ] ⟫ (Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ) ⟩ 

      perform `ty-ctx-subst T (ctx-id (now Γ) {Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ})` on both sides, we get 
        ty-ctx-subst T (ctx-id (now Γ)) (constantly-ty T ⟪ [ z≤n {m} , hom-id V {x} ] , refl ⟫ (t ⟨ [ m , x ] , γ ⟩'))
      ≡ ty-ctx-subst T (ctx-id (now Γ)) (t ⟨ [ 0 , x ] , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ ⟩') 
      of type 
        constantly-ty T ⟨ [ m , x ] , γ ⟩ = T ⟨ x , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ ⟩
      which is WHAT WE WANT
    -}
    where
      open ≡-Reasoning
      proof : Γ ⟪ [ z≤n {zero} , hom-id V {x} ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γ) ≡ Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ)
      proof =
        begin
          Γ ⟪ [ z≤n {zero} , hom-id V {x} ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γ)
        ≡˘⟨ ctx-comp Γ ⟩
          Γ ⟪ [ ≤-trans (z≤n {zero}) (z≤n) , (_∙_) V (hom-id V) (hom-id V {x}) ] ⟫ γ
        ≡⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩ 
          Γ ⟪ [ ≤-trans (z≤n) z≤n , hom-id V {x} ] ⟫ γ
        ≡˘⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , hom-idʳ V ]) ⟩
          Γ ⟪ [ ≤-trans (z≤n) z≤n , (_∙_) V (hom-id V {x}) (hom-id V) ] ⟫ γ
        ≡⟨ ctx-comp Γ ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ z≤n , hom-id V {x} ] ⟫ γ)
        ≡⟨ cong (Γ ⟪ [ z≤n , hom-id V ] ⟫_) refl ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ) ∎
      proof' : Γ ⟪ [ z≤n {zero} , hom-id V {x} ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γ) ≡ Γ ⟪ [ z≤n , hom-id V ] ⟫ γ
      proof' =
        begin
          Γ ⟪ [ z≤n {zero} , hom-id V {x} ] ⟫ (Γ ⟪ [ z≤n , hom-id V ] ⟫ γ)
        ≡˘⟨ ctx-comp Γ ⟩
          Γ ⟪ [ ≤-trans (z≤n {zero}) z≤n , (_∙_) V (hom-id V) (hom-id V {x}) ] ⟫ γ
        ≡⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩ 
          Γ ⟪ [ ≤-trans z≤n ≤-refl , hom-id V {x} ] ⟫ γ
        ≡˘⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , hom-idʳ V ]) ⟩
          Γ ⟪ [ ≤-trans z≤n ≤-refl , (_∙_) V (hom-id V {x}) (hom-id V) ] ⟫ γ
        ≡⟨ ctx-comp Γ ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ (Γ ⟪ [ ≤-refl , hom-id V {x} ] ⟫ γ)
        ≡⟨ cong (Γ ⟪ [ z≤n , hom-id V ] ⟫_) (ctx-id Γ) ⟩
          Γ ⟪ [ z≤n , hom-id V ] ⟫ γ ∎
      proof'' : constantly-tm (unconstantly-tm t) ⟨ [ m , x ] , γ ⟩' ≡ t ⟨ [ m , x ] , γ ⟩'
      proof'' = 
        begin
          constantly-tm (unconstantly-tm t) ⟨ [ m , x ] , γ ⟩'
        ≡⟨⟩
          ty-ctx-subst T (ctx-id (now Γ)) (t ⟨ [ 0 , x ] , Γ ⟪ [ z≤n {m} , hom-id V ] ⟫ γ ⟩')
        ≡˘⟨ cong (ty-ctx-subst T (ctx-id (now Γ))) (Tm.naturality t [ z≤n {m} , hom-id V ] refl) ⟩
          ty-ctx-subst T (ctx-id (now Γ)) (constantly-ty T ⟪ [ z≤n {m} , hom-id V ] , refl ⟫ (t ⟨ [ m , x ] , γ ⟩'))
        ≡⟨⟩
          T ⟪ hom-id V {x} , trans (ctx-id (now Γ)) (ctx-id (now Γ)) ⟫ (constantly-ty T ⟪ [ z≤n {m} , hom-id V ] , refl ⟫ (t ⟨ [ m , x ] , γ ⟩'))
        ≡⟨⟩
          T ⟪ hom-id V , trans (ctx-id (now Γ)) (ctx-id (now Γ)) ⟫ (T ⟪ hom-id V , proof ⟫ (t ⟨ [ m , x ] , γ ⟩'))
        ≡⟨ ty-cong-2-1 T (hom-idˡ V) ⟩
          T ⟪ hom-id V , proof' ⟫ (t ⟨ [ m , x ] , γ ⟩')
        ≡⟨⟩
          constantly-ty T ⟪ [ ≤-refl , hom-id V ] , ctx-id Γ ⟫ (t ⟨ [ m , x ] , γ ⟩')
        ≡⟨ Tm.naturality t {x = [ m , x ]} {y = [ m , x ]} {γy = γ} {γx = γ} [ ≤-refl , hom-id V ] (ctx-id Γ) ⟩ 
          t ⟨ [ m , x ] , γ ⟩' ∎
    
  -- β-rule
  constantly-ty-β : (t : Tm (now Γ) T) → unconstantly-tm (constantly-tm t) ≅ᵗᵐ t
  eq (constantly-ty-β t) {x} γ = Tm.naturality t {x = x} {y = x} {γy = now Γ ⟪ hom-id V ⟫ γ} {γx = γ} (hom-id V) (trans (ctx-id (now Γ)) (ctx-id (now Γ)))
    {- GOAL: 
      γ : now Γ ⟨ x ⟩
      RHS : unconstantly-tm (constantly-tm t) ⟨ x , γ ⟩' ≡ t ⟨ x , γ ⟩'

        unconstantly-tm (constantly-tm t) ⟨ x , γ ⟩'
      ≡⟨⟩
        ty-ctx-subst T (ctx-id (now Γ) {x} {γ}) (constantly-tm t ⟨ [ 0 , x ] , γ ⟩')
      ≡⟨⟩
        ty-ctx-subst T (ctx-id (now Γ)) (t ⟨ x , Γ ⟪ 0≤0 , hom-id V ⟫ γ ⟩ : T ⟨ x , Γ ⟪ [ 0≤0 , hom-id V ] ⟫ γ ⟩ = constantly-ty T ⟨ [ 0 , x ] , γ ⟩)
      ≡⟨⟩
        ty-ctx-subst T (ctx-id (now Γ)) (t ⟨ x , now Γ ⟪ hom-id V ⟫ γ ⟩)
      ≡⟨⟩
        T ⟪ hom-id V , trans (ctx-id (now Γ)) (ctx-id (now Γ)) ⟫ (t ⟨ x , now Γ ⟪ hom-id V ⟫ γ ⟩)
      ≡⟨ Tm.naturality t {x = x} {y = x} {γy = now Γ ⟪ hom-id V ⟫ γ} {γx = γ} (hom-id V) (trans (ctx-id (now Γ)) (ctx-id (now Γ))) ⟩
        t ⟨ x , γ ⟩' ∎
    -}

{-
  now Γ ⊢ T ≅ᵗʸ S
  -----------------------------------------
  Γ ⊢ constantly-ty T ≅ᵗʸ constantly-ty S

  The action of `constantly` on types respects equivalence of types.
-}
constantly-ty-cong : {T : Ty (now Γ)} {S : Ty (now Γ)} → T ≅ᵗʸ S → constantly-ty T ≅ᵗʸ constantly-ty S
func (from (constantly-ty-cong T=S)) = func (from T=S)
_↣_.naturality (from (constantly-ty-cong T=S)) = _↣_.naturality (from T=S)
func (to (constantly-ty-cong T=S)) = func (to T=S)
_↣_.naturality (to (constantly-ty-cong T=S)) = _↣_.naturality (to T=S)
eq (isoˡ (constantly-ty-cong T=S)) = eq (isoˡ T=S)
eq (isoʳ (constantly-ty-cong T=S)) = eq (isoʳ T=S)

module _ {T : Ty (now Γ)} where
  {-
    now Γ ⊢ t s : T   now Γ ⊢ t ≅ᵗᵐ s
    --------------------------------------------------------------------------------
    Γ ⊢ constantly-tm t : constantly-ty T   Γ ⊢ constantly-tm t : constantly-ty T 
    Γ ⊢ constantly-tm t ≅ᵗᵐ constantly-tm s

    The action of `constantly` on terms (i.e., the term constructor `mod-intro(_)`) respects equivalence of terms. 
  -}
  constantly-tm-cong : {t s : Tm (now Γ) T} → t ≅ᵗᵐ s → constantly-tm t ≅ᵗᵐ constantly-tm s
  eq (constantly-tm-cong t=s) γ = eq t=s (Γ ⟪ [ z≤n , hom-id V ] ⟫ γ)

  {-
    Γ ⊢ t s : constantly-ty T   Γ ⊢ t ≅ᵗᵐ s
    ---------------------------------------------------------------
    now Γ ⊢ unconstantly-tm t : T   now Γ ⊢ unconstantly-tm s : T
    now Γ ⊢ unconstantly-tm t ≅ᵗᵐ unconstantly-tm s

    The inverse of the action of `constantly` on terms respects equivalence of terms. 
  -}
  unconstantly-tm-cong : {t s : Tm Γ (constantly-ty T)} → t ≅ᵗᵐ s → unconstantly-tm t ≅ᵗᵐ unconstantly-tm s
  eq (unconstantly-tm-cong t=s) {x} γ = cong (ty-ctx-subst T (ctx-id (now Γ))) (eq t=s {[ 0 , x ]} γ)

module _ {T S : Ty (now Γ)} where
  {-
    now Γ ⊢ T ≅ᵗʸ S   now Γ ⊢ s : S
    --------------------------------------------------------------------------------
    Γ ⊢ ι[ constantly-ty-cong T=S ] constantly-tm s ≅ᵗᵐ constantly-tm (ι[ T=S ] s)

    The action of `constantly` on terms (i.e., the term constructor `mod-intro(_)`) respects typing judgement conversion.
  -}
  constantly-tm-ι : (T=S : T ≅ᵗʸ S) (s : Tm (now Γ) S) →
                    ι[ constantly-ty-cong T=S ] constantly-tm s ≅ᵗᵐ constantly-tm (ι[ T=S ] s)
  eq (constantly-tm-ι T=S s) _ = refl

  unconstantly-tm-ι : (T=S : T ≅ᵗʸ S) (s : Tm Γ (constantly-ty S)) →
                      ι[ T=S ] unconstantly-tm s ≅ᵗᵐ unconstantly-tm (ι[ constantly-ty-cong T=S ] s)
  eq (unconstantly-tm-ι T=S s) γ = sym (_↣_.naturality (to T=S))

{-
  σ : Δ ⇒ Γ   now Γ ⊢ T
  --------------------------------------------------
  now-subst σ : now Δ ⇒ now Γ   Γ ⊢ constantly-ty T
  now Δ ⊢ T [ now-subst σ ]
  Δ ⊢ constantly-ty (T [ now-subst σ ])
  ------------------------------------------------------------------
  Δ ⊢ (constantly-ty T) [ σ ] ≅ᵗʸ constantly-ty (T [ now-subst σ ])

  The action of `constantly` on types (i.e., `⟨ constantly ∣_⟩`) commutes with type substitutions. 
-}
constantly-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ)} → (constantly-ty T) [ σ ] ≅ᵗʸ constantly-ty (T [ now-subst σ ])
-- from : (constantly-ty T) [ σ ] ↣ constantly-ty (T [ now-subst σ ])
-- T = (constantly-ty T) [ σ ]
-- S = constantly-ty (T [ now-subst σ ])
func (from (constantly-ty-natural σ {T})) = ty-ctx-subst T (_⇒_.naturality σ)
  {-
    RHS : 
      (constantly-ty T) [ σ ] ⟨ [ m , x ] , γ ⟩ → constantly-ty (T [ now-subst σ ]) ⟨ [ m , x ] , γ ⟩
    = constantly-ty T ⟨ [ m , x ] , func σ γ ⟩ → T [ now-subst σ ] ⟨ x , Δ ⟪ [ z≤m , hom-id V {x} ] ⟫ γ ⟩
    = constantly-ty T ⟨ [ m , x ] , func σ γ ⟩ → T ⟨ x , func (now-subst σ) (Δ ⟪ [ z≤m , hom-id V {x} ] ⟫ γ) ⟩
    = constantly-ty T ⟨ [ m , x ] , func σ γ ⟩ → T ⟨ x , func σ (Δ ⟪ [ z≤m , hom-id V {x} ] ⟫ γ) ⟩
    = T ⟨ x , Γ ⟪ [ z≤m , hom-id V {x} ] ⟫ (func σ γ) ⟩ → T ⟨ x , func σ (Δ ⟪ [ z≤m , hom-id V {x} ] ⟫ γ) ⟩
    = ty-ctx-subst T {δ = Γ ⟪ [ z≤m , hom-id V {x} ] ⟫ (func σ γ)} {δ' = func σ (Δ ⟪ [ z≤m , hom-id V {x} ] ⟫ γ)} (_⇒_.naturality σ) 
    = T ⟪ hom-id V {x} , _ ⟫ _
  -}
_↣_.naturality (from (constantly-ty-natural σ {T})) = ty-cong-2-2 T (hom-idᵒ V)
  {-
    RHS : 
                                  S ⟪ [ m≤n , g ] , eγ ⟫_
            S ⟨ [ m , x ] , γx ⟩ ←--------------------- S ⟨ [ n , y ] , γy ⟩
                      ↑                                    ↑
         func (T ↣ S) |                                    | func (T ↣ S)
                      |                                    |
            T ⟨ [ m , x ] , γx ⟩ ←--------------------- T ⟨ [ n , y ] , γy ⟩ ∋ t
                                  T ⟪ [ m≤n , g ] , eγ ⟫_
    with T ⟨ [ m , x ] , γx ⟩ = (constantly-ty T) [ σ ] ⟨ [ m , x ] , γx ⟩
                              = constantly-ty T ⟨ [ m , x ] , func σ γx ⟩
                              = T ⟨ x , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ (func σ γx) ⟩ 
         S ⟨ [ m , x ] , γx ⟩ = constantly-ty (T [ now-subst σ ]) ⟨ [ m , x ] , γx ⟩
                              = T [ now-subst σ ] ⟨ x , Δ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γx ⟩
                              = T ⟨ x , func σ (Δ ⟪ [ z≤m , hom-id V {x} ] ⟫ γ) ⟩
         T ⟪ [ m≤n , g ] , eγ ⟫_ = (constantly-ty T) [ σ ] ⟪ [ m≤n , g ] , eγ ⟫_
                                 = constantly-ty T ⟪ [ m≤n , g ] , new-proof ⟫_
                                 = T ⟪ g , new-new-proof ⟫_
         S ⟪ [ m≤n , g ] , eγ ⟫_ = constantly-ty (T [ now-subst σ ]) ⟪ [ m≤n , g ] , eγ ⟫_
                                 = T [ now-subst σ ] ⟪ g , new-proof ⟫_
                                 = T ⟪ g , func (now-subst σ) new-proof ⟫_
    (RHS) func (T ↣ S) = func {[ n , y ]} {γy}
                      = T ⟨ y , Γ ⟪ [ 0≤n , hom-id V {y} ] ⟫ (func σ γy) ⟩ → T ⟨ y , func σ (Δ ⟪ [ 0≤n , hom-id V {y} ] ⟫ γy) ⟩
                      = T ⟪ hom-id V {y}, ...
    (LHS) func (T ↣ S) = func {[ m , x ]} {γx}
                      = T ⟨ x , Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ (func σ γx) ⟩ → T ⟨ x , func σ (Δ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γx) ⟩
                      = T ⟪ hom-id V {x}, ...

    ty-cong-2-2 T (e-hom : hom-id V {y} ∙ g ≡ g ∙ hom-id V {x})
                            T ⟪ f , ef ⟫_ 
              T ⟨ x , γx ⟩ ←--------------- T ⟨ y , γy ⟩ 
                    ↑                             ↑
    T ⟪ f' , ef' ⟫_ |                             | T ⟪ g , eg ⟫_ 
                    |                             ∣
              T ⟨ z , γz ⟩ ←--------------- T ⟨ w , γw ⟩ ∋ t
                            T ⟪ g' , eg' ⟫_ 
  -}
-- to : constantly-ty (T [ now-subst σ ]) ↣ (constantly-ty T) [ σ ]
func (to (constantly-ty-natural σ {T})) = ty-ctx-subst T (sym (_⇒_.naturality σ))
_↣_.naturality (to (constantly-ty-natural σ {T})) = ty-cong-2-2 T (hom-idᵒ V)
-- isoˡ : to ⊙ from ≅ⁿ id-trans T of type T ↣ T
eq (isoˡ (constantly-ty-natural σ {T})) t = ty-ctx-subst-inverseˡ T
  {-
    RHS : 
      func (to ⊙ from) t ≡ func (id-trans T) t
    = (func to ∘ func from) t ≡ t
    = func to (func from t) ≡ t
    = ty-ctx-subst T (sym (_⇒_.naturality σ)) (ty-ctx-subst T (_⇒_.naturality σ) t)
  -}
-- isoʳ : from ⊙ to ≅ⁿ id-trans S
eq (isoʳ (constantly-ty-natural σ {T})) t = ty-ctx-subst-inverseʳ T
  {-
    RHS :
      func (from ⊙ to) t ≡ func (id-trans S) t
    = func from (func to t) ≡ t
    = ty-ctx-subst T (_⇒_.naturality σ) (ty-ctx-subst T (sym (_⇒_.naturality σ)) t) ≡ t
  -}

-- A proof of the natural property of any closed type over V
instance
  constantly-closed : {A : ClosedTy V} {{_ : IsClosedNatural A}} → IsClosedNatural (constantly-ty A)
  closed-natural {{constantly-closed}} σ = ≅ᵗʸ-trans (constantly-ty-natural σ) (constantly-ty-cong (closed-natural (now-subst σ)))

module _ (σ : Δ ⇒ Γ) {T : Ty (now Γ)} where
  {-
    now Γ ⊢ t : T
    -------------------------------------------------------
    Γ ⊢ constantly-tm t : constantly-ty T     σ : Δ ⇒ Γ
    -------------------------------------------------------
    Δ ⊢ (constantly-tm t) [ σ ]' : (constantly-ty T) [ σ ]


    now Γ ⊢ t : T
    -----------------------------------------------
    now Δ ⊢ t [ now-subst σ ]' : T [ now-subst σ ]
    ----------------------------------------------------------------------------
    Δ ⊢ constantly-tm (t [ now-subst σ ]') : constantly-ty (T [ now-subst σ ])
    Δ ⊢ (constantly-ty T) [ σ ] ≅ᵗʸ constantly-ty (T [ now-subst σ ])
    ----------------------------------------------------------------------------------------------
    Δ ⊢ ι[ constantly-ty-natural σ ] constantly-tm (t [ now-subst σ ]') : (constantly-ty T) [ σ ]
  -}
  constantly-tm-natural : (t : Tm (now Γ) T) →
                        (constantly-tm t) [ σ ]' ≅ᵗᵐ ι[ constantly-ty-natural σ ] constantly-tm (t [ now-subst σ ]') -- of type `(constantly-ty T) [ σ ]`
  eq (constantly-tm-natural t) {[ m , x ]} δ = sym (Tm.naturality t (hom-id V) _)
    {- 
      δ : Δ ⟪ [ m , x ] ⟫
      RHS : 
        (constantly-tm t) [ σ ]' ⟨ [ m , x ] , δ ⟩ ≡ ι[ constantly-ty-natural σ ] constantly-tm (t [ now-subst σ ]') ⟨ [ m , x ] , δ ⟩

        constantly-ty-natural σ {T} : (constantly-ty T) [ σ ] ≅ᵗʸ constantly-ty (T [ now-subst σ ])
    -}

  {-
    LHS of the equivalence : 
      Γ ⊢ t : constantly-ty T
      now Γ ⊢ unconstantly-tm t : T     now-subst σ : now Δ ⇒ now Γ
      -----------------------------------------------------------------
      now Δ ⊢ (unconstantly-tm t) [ now-subst σ ]' : T [ now-subst σ ]
    
    RHS of the equivalence : 
      Δ ⊢ t [ σ ]' : constantly-ty T [ σ ]      Δ ⊢ constantly-ty (T [ now-subst σ ])
      constantly-ty-natural σ {T} : (constantly-ty T) [ σ ] ≅ᵗʸ constantly-ty (T [ now-subst σ ])
      ---------------------------------------------------------------------------------------------
      Δ ⊢ ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]') : constantly-ty (T [ now-subst σ ])
      ----------------------------------------------------------------------------------------
      now Δ ⊢ unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]')) : T [ now-subst σ ]
  -}
  unconstantly-tm-natural : (t : Tm Γ (constantly-ty T)) →
                          (unconstantly-tm t) [ now-subst σ ]' ≅ᵗᵐ unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]'))
  eq (unconstantly-tm-natural t) {x} δ = sym (ty-cong-2-1 T (hom-idˡ V))
    {-
      δ : now Δ ⟨ x ⟩
      RHS : 
        (unconstantly-tm t) [ now-subst σ ]' ⟨ x , δ ⟩' ≡ unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]')) ⟨ x , δ ⟩'

      where
        open ≡-Reasoning
        proof : now Γ ⟪ hom-id V ⟫ func (now-subst σ) (now Γ ⟪ hom-id V {x} ⟫ (func σ δ)) ≡ func (now-subst σ) (func σ (now Δ ⟪ hom-id V {x} ⟫ δ))
        proof = trans (_⇒_.naturality (now-subst σ)) (cong (func (now-subst σ)) (trans (ctx-id (now Δ)) (ctx-id (now Δ))))
          {-
            {Γ = now Γ} (σ = now-subst σ) (f = hom-id V) {δy = now Γ ⟪ hom-id V {x} ⟫ (func σ δ)} {δx = func σ (now Δ ⟪ hom-id V {x} ⟫ δ)} (eγ-yx = trans (ctx-id (now Δ)) (ctx-id (now Δ)) : now Γ ⟪ hom-id V ⟫ δy ≡ δx)
                    -- trans (ctx-id (now Γ)) (_⇒_.naturality σ) : now Γ ⟪ hom-id V ⟫ (now Γ ⟪ hom-id V {x} ⟫ (func σ δ)) ≡ func σ (now Δ ⟪ hom-id V {x} ⟫ δ)
          -}
        
        proof' : (unconstantly-tm t) [ now-subst σ ]' ⟨ x , δ ⟩' ≡ unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]')) ⟨ x , δ ⟩'
        proof' = 
          begin
            (unconstantly-tm t) [ now-subst σ ]' ⟨ x , δ ⟩'
          ≡⟨⟩
            unconstantly-tm t ⟨ x , func (now-subst σ) δ ⟩'
          ≡⟨⟩
            ty-ctx-subst T (ctx-id (now Γ)) (t ⟨ [ 0 , x ] , func (now-subst σ) δ ⟩')
          ≡⟨⟩
            T ⟪ hom-id V , trans (ctx-id (now Γ)) (ctx-id (now Γ)) ⟫ (t ⟨ [ 0 , x ] , func σ δ ⟩')
          ≡˘⟨ ty-cong-2-1 T (hom-idˡ V) ⟩
            T ⟪ hom-id V , proof ⟫ (T ⟪ hom-id V , trans (ctx-id (now Γ)) (_⇒_.naturality σ) ⟫ (t ⟨ [ 0 , x ] , func σ {[ 0 , x ]} δ ⟩))
          ≡⟨⟩
            (T [ now-subst σ ]) ⟪ hom-id V , trans (ctx-id (now Δ)) (ctx-id (now Δ)) ⟫ (T ⟪ hom-id V , trans (ctx-id (now Γ)) (_⇒_.naturality σ) ⟫ (t ⟨ [ 0 , x ] , func σ {[ 0 , x ]} δ ⟩))
          ≡⟨⟩
            (T [ now-subst σ ]) ⟪ hom-id V , trans (ctx-id (now Δ)) (ctx-id (now Δ)) ⟫ ((ty-ctx-subst T (_⇒_.naturality σ)) (t ⟨ [ 0 , x ] , func σ {[ 0 , x ]} δ ⟩))
                  -- t ⟨ [ 0 , x ] , func σ {[ 0 , x ]} δ ⟩ : T ⟪ x , Γ ⟪ [ 0≤0 , hom-id V {x} ] ⟫ (func σ δ) ⟫
                  -- _⇒_.naturality σ : Γ ⟪ [ 0≤0 , hom-id V {x} ] ⟫ (func σ δ) ≡ func σ (Δ ⟪ [ z≤0 , hom-id V {x} ] ⟫ δ)
          ≡⟨⟩
            (T [ now-subst σ ]) ⟪ hom-id V , trans (ctx-id (now Δ)) (ctx-id (now Δ)) ⟫ (func (from (constantly-ty-natural σ)) (t ⟨ [ 0 , x ] , func σ δ ⟩))
          ≡⟨⟩
            (T [ now-subst σ ]) ⟪ hom-id V , trans (ctx-id (now Δ)) (ctx-id (now Δ)) ⟫ (func (to (≅ᵗʸ-sym (constantly-ty-natural σ))) (t ⟨ [ 0 , x ] , func σ δ ⟩))
          ≡⟨⟩
            (T [ now-subst σ ]) ⟪ hom-id V , trans (ctx-id (now Δ)) (ctx-id (now Δ)) ⟫ ((ι[ ≅ᵗʸ-sym (constantly-ty-natural σ) ] (t [ σ ]')) ⟨ [ 0 , x ] , δ ⟩')
          ≡⟨⟩
            (T [ now-subst σ ]) ⟪ hom-id V , trans (ctx-id (now Δ)) (ctx-id (now Δ)) ⟫ ((ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]')) ⟨ [ 0 , x ] , δ ⟩')
          ≡⟨⟩
            ty-ctx-subst (T [ now-subst σ ]) (ctx-id (now Δ)) ((ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]')) ⟨ [ 0 , x ] , δ ⟩')
          ≡⟨⟩
            unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]')) ⟨ x , δ ⟩'
    -}

-- A modal version of the eliminator for booleans for the constantly modality.
constantly-if'_then'_else'_ : {T : Ty Γ} → Tm Γ (constantly-ty Bool') → Tm Γ T → Tm Γ T → Tm Γ T
constantly-if' c then' t else' f ⟨ n , γ ⟩' = if c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ with c ⟨ m , γ' ⟩' | c ⟨ n , γ ⟩' | Tm.naturality c m≤n eγ
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | false | .false | refl = Tm.naturality f m≤n eγ
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | true  | .true  | refl = Tm.naturality t m≤n eγ
