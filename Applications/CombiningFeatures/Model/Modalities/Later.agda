--------------------------------------------------
-- The earlier-later dependent adjunction
--------------------------------------------------
open import Model.BaseCategory

module Applications.CombiningFeatures.Model.Modalities.Later (V : BaseCategory) where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.String using (String)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.Type.Function
open import Model.CwF-Structure.Reflection.SubstitutionSequence

open BaseCategory

ω×V : BaseCategory
ω×V = ω ⊗ V

private
  variable
    m n : ℕ
    x y : Ob V
    Γ Δ Θ : Ctx ω×V

infixl 12 _⟨$⟩_
infixl 12 _⊛_
infixr 4 löb[_∈▻'_]_


--------------------------------------------------
-- The "earlier" Context operation

{-
  data _≤_ : Rel ℕ 0ℓ where
    z≤n : ∀ {n}                 → 0  ≤ n
    s≤s : ∀ {m n} (m≤n : m ≤ n) → m+1 ≤ n+1

                                            Γ ⟪ [ m≤n , g ] ⟫_
                      Γ ⟨ [ m , x ] ⟩ ←-------------------------- Γ ⟨ [ n , y ] ⟩
                              ↑                                          ↑
  Γ ⟪ [ m≤m+1 , hom-id V ] ⟫_ |                                          | Γ ⟪ [ n≤n+1 , hom-id V ] ⟫_
                              |                                          |
                      Γ ⟨ [ m+1 , x ] ⟩ ←---------------------- Γ ⟨ [ n+1 , y ] ⟩ ∋ γ
                                         Γ ⟪ [ m+1≤n+1 , g ] ⟫_
-}
ctx-m≤1+n : (Γ : Ctx ω×V) {m≤n : m ≤ n} {g : Hom V x y} {γ : Γ ⟨ [ suc n , y ] ⟩} 
          → Γ ⟪ [ m≤n , g ] ⟫ (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ γ) ≡ Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ (Γ ⟪ [ s≤s m≤n , g ] ⟫ γ)
ctx-m≤1+n {m} {n} Γ {m≤n} {g} {γ} =
  begin
    Γ ⟪ [ m≤n , g ] ⟫ (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ γ)
  ≡˘⟨ ctx-comp Γ ⟩  
    Γ ⟪ [ ≤-trans m≤n (n≤1+n n) , (_∙_) V (hom-id V) g ] ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩ 
    Γ ⟪ [ ≤-trans (n≤1+n m) (s≤s m≤n) , g ] ⟫ γ
  ≡˘⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , hom-idʳ V ]) ⟩
    Γ ⟪ [ ≤-trans (n≤1+n m) (s≤s m≤n) , (_∙_) V g (hom-id V) ] ⟫ γ
  ≡⟨ ctx-comp Γ ⟩
    Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ (Γ ⟪ [ s≤s m≤n , g ] ⟫ γ) ∎
  where open ≡-Reasoning

{-  
  Γ = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  -----------------------------
  ◄ Γ = ✲₁ ← ✲₂ ← ✲₃ ... 

  The context operator `_,lock⟨ later ⟩` of modality `later` 
-}
◄ : Ctx ω×V → Ctx ω×V
◄ Γ ⟨ [ m , x ] ⟩ = Γ ⟨ [ suc m , x ] ⟩
  -- Disgards information about Γ ⟨ [ 0 , _ ] ⟩
◄ Γ ⟪ [ m≤n , g ] ⟫ γ = Γ ⟪ [ s≤s m≤n , g ] ⟫ γ
ctx-id (◄ Γ) = ctx-id Γ
ctx-comp (◄ Γ) = ctx-comp Γ

{-
              Δ⟨✲₀⟩ ← Δ⟨✲₁⟩ ← Δ⟨✲₂⟩ ← Δ⟨✲₃⟩ ...
          σ :   ↓        ↓       ↓        ↓
              Γ⟨✲₀⟩ ← Γ⟨✲₁⟩ ← Γ⟨✲₂⟩ ← Γ⟨✲₃⟩ ...

              Δ⟨✲₁⟩ ← Δ⟨✲₂⟩ ← Δ⟨✲₃⟩ ...
  ◄-subst σ :   ↓        ↓       ↓       
              Γ⟨✲₁⟩ ← Γ⟨✲₂⟩ ← Γ⟨✲₃⟩ ...

  The action of ◄ on the morphisms (i.e., context substitutions) of Psh(ω×V)
-}
◄-subst : (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {[ m , x ]} = func σ {[ suc m , x ]}
naturality (◄-subst σ) {f = [ m≤n , g ]} = naturality σ {f = [ s≤s m≤n , g ]}

{-
  -- The operations on types and terms are not used anywhere
  ◅-ty : Ty Γ → Ty (◄ Γ)
  type (◅-ty T) n γ = T ⟨ suc n , γ ⟩
  morph (◅-ty T) m≤n eγ = T ⟪ s≤s m≤n , eγ ⟫
  morph-cong (◅-ty T) e = morph-cong T (cong s≤s e)
  morph-id (◅-ty T) t = morph-id T t
  morph-comp (◅-ty T) k≤m m≤n = morph-comp T (s≤s k≤m) (s≤s m≤n)

  ◅-tm : {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (◅-ty T)
  term (◅-tm t) n γ = t ⟨ suc n , γ ⟩'
  naturality (◅-tm t) m≤n eγ = naturality t (s≤s m≤n) eγ
-}

{-
                          ✲₁ ← ✲₂ ← ✲₃ ...
  from-earlier Γ :      ↙     ↙    ↙  
                      ✲₀  ← ✲₁ ← ✲₂ ...
  
  A morphism constructor that identifies each downward diagonal arrow with the closest bottom-right arrow ←
-}
from-earlier : (Γ : Ctx ω×V) → ◄ Γ ⇒ Γ
func (from-earlier Γ) {[ n , _ ]} = Γ ⟪ [ n≤1+n n , hom-id V ] ⟫_
naturality (from-earlier Γ) = ctx-m≤1+n Γ


--------------------------------------------------
-- Congruence, naturality and functoriality for earlier

{- 
  σ ≅ˢ τ
  -----------------------
  ◄-subst σ ≅ˢ ◄-subst τ

  The action of ◄ on the morphisms of Psh(ω×V) respects equivalence of morphisms/substitutions
-}
◄-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ◄-subst σ ≅ˢ ◄-subst τ
eq (◄-subst-cong σ=τ) δ = eq σ=τ δ

{-
  -- The operations on types and terms are not used anywhere

  ◅-ty-cong : {T : Ty Γ} {T' : Ty Γ} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
  ◅-ty-cong : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
  func (from (◅-ty-cong T=T')) = func (from T=T')
  naturality (from (◅-ty-cong T=T')) = naturality (from T=T')
  func (to (◅-ty-cong T=T')) = func (to T=T')
  naturality (to (◅-ty-cong T=T')) = naturality (to T=T')
  eq (isoˡ (◅-ty-cong T=T')) t = eq (isoˡ T=T') t
  eq (isoʳ (◅-ty-cong T=T')) t = eq (isoʳ T=T') t

  ◅-tm-cong : {T : Ty Γ} {t t' : Tm Γ T} → t ≅ᵗᵐ t' → ◅-tm t ≅ᵗᵐ ◅-tm t'
  eq (◅-tm-cong t=t') γ = eq t=t' γ

  ◅-tm-ι : {T : Ty Γ} {T' : Ty Γ} (T=T' : T ≅ᵗʸ T') (t : Tm Γ T') →
            ◅-tm (ι[ T=T' ] t) ≅ᵗᵐ ι[ ◅-ty-cong T=T' ] (◅-tm t)
  eq (◅-tm-ι T=T' t) γ = refl

  module _ {Δ : Ctx ω} {Γ : Ctx ω} (σ : Δ ⇒ Γ) {T : Ty Γ} where
    ◅-ty-natural : (◅-ty T) [ ◄-subst σ ] ≅ᵗʸ ◅-ty (T [ σ ])
    func (from ◅-ty-natural) = id
    naturality (from ◅-ty-natural) _ = refl
    func (to ◅-ty-natural) = id
    naturality (to ◅-ty-natural) _ = refl
    eq (isoˡ ◅-ty-natural) _ = refl
    eq (isoʳ ◅-ty-natural) _ = refl

    ◅-tm-natural : (t : Tm Γ T) → (◅-tm t) [ ◄-subst σ ]' ≅ᵗᵐ ι[ ◅-ty-natural ] (◅-tm (t [ σ ]'))
    eq (◅-tm-natural t) _ = refl
-}

{-
          ◄-subst σ
    ◄ Δ =============⇒ ◄ Γ
     ║                   ║
     ║                   ║
     ⇓                   ⇓
     Δ ================⇒ Γ
              σ

  The morphism constructor `from-earlier` Psh(ω×V) commutes with substitution composition. 
-}
from-earlier-natural : (σ : Δ ⇒ Γ) → from-earlier Γ ⊚ ◄-subst σ ≅ˢ σ ⊚ from-earlier Δ
eq (from-earlier-natural σ) δ = naturality σ

-- The action of ◄ on the morphisms of Psh(ω×V) preserves the identity morphisms.
◄-subst-id : ◄-subst (id-subst Γ) ≅ˢ id-subst (◄ Γ)
eq ◄-subst-id _ = refl

-- The action of ◄ on the morphisms of Psh(ω×V) commutes with substitution composition. 
◄-subst-⊚ : (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → ◄-subst (τ ⊚ σ) ≅ˢ ◄-subst τ ⊚ ◄-subst σ
eq (◄-subst-⊚ τ σ) _ = refl

-- A proof that ◄ is a functor
instance
  ◄-is-functor : IsCtxFunctor ◄
  ctx-map {{◄-is-functor}} = ◄-subst
  ctx-map-cong {{◄-is-functor}} = ◄-subst-cong
  ctx-map-id {{◄-is-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-is-functor}} = ◄-subst-⊚


--------------------------------------------------
-- The later modality and corresponding term formers

{-
  ◄ Γ ⊢ T = ✲₁ ← ✲₂ ← ✲₃ ... 
  ---------------------------------
  Γ ⊢ ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 

  ◄ Γ vs. ▻ T:
    - The former disgards some information ...
    - The latter keeps all the information but delays access by one unit ...
-}
▻ : Ty (◄ Γ) → Ty Γ
▻ T ⟨ [ 0 , _ ]  , _ ⟩ = ⊤
▻ T ⟨ [ suc m , x ] , γ ⟩ = T ⟨ [ m , x ] , γ ⟩
▻ T ⟪ [ z≤n , _ ] , _ ⟫ _ = tt
▻ T ⟪ [ s≤s m≤n , g ] , eγ ⟫ t = T ⟪ [ m≤n , g ] , eγ ⟫ t
ty-cong (▻ T) {f = [ z≤n , _ ]} {f' = [ z≤n , _ ]} e = refl
ty-cong (▻ T) {f = [ s≤s m≤n , _ ]} {f' = [ s≤s .m≤n , _ ]} refl = ty-cong T refl
ty-id (▻ T) {[ 0 , _ ]} = refl
ty-id (▻ T) {[ suc m , _ ]} = ty-id T
ty-comp (▻ T) {f = [ z≤n , _ ]} {g = [ m≤n , _ ]} = refl
ty-comp (▻ T) {f = [ s≤s k≤m , _ ]} {g = [ s≤s m≤n , _ ]} = ty-comp T

{-
  Γ ⊢ T                         = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ T [ from-earlier Γ ]    = ✲₁ ← ✲₂ ← ✲₃ ... 
  ----------------------------------------------------
  Γ ⊢ ▻' T                      = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
    with ▻' T ⟨ [ 0 , x ] , γ ⟩ = ⊤
         ▻' T ⟨ [ m+1 , x ] , γ ⟩ = T ⟨ [ m , x ] , Γ ⟪ m≤m+1 ⟫ γ ⟩
         
                             ... ✲m-1 ←  ... 
                                 ∕
    ▻' T ⟪ [ 0≤m , g ] , eγ ⟫_ ∕   
  = ? ↦ tt                  ↙ 
                          ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 

                                                   ... ✲m ←  ... 
                                                      ∕
    ▻' T ⟪ [ m+1≤n+1 , g ] , eγ ⟫_                  ∕   
  = T ⟪ [ m≤n , g ] , ty-subst-⟪_,_⟫-proof ... ⟫_ ∕ 
                                               ↙ 
                                         ... ✲n ← ... 

  ▻ T vs. ▻' T:
    - The former keeps all information.
    - The latter disgards the currently available information.
-}
▻' : Ty Γ → Ty Γ
▻' {Γ = Γ} T = ▻ (T [ from-earlier Γ ])
  {-

    Γ ⊢ ▻' T ⟪ [ z≤n , g ] , eγ ⟫_ = ? ↦ tt
    Γ ⊢ ▻' T ⟪ [ s≤s m≤n , g ] , eγ ⟫_ = T ⟪ [ m≤n , g ] , Γ ⟪ m≤m+1 , eγ ⟫_
  -}

module _ {T : Ty (◄ Γ)} where
  {-
    ◄ Γ ⊢ t : ✲₁ ← ✲₂ ← ✲₃ ... 
    -----------------------------------
    Γ ⊢ next t : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ...
    
    A term constructor for type `▻ T`; delays access to informaiton by one step; "saves" a term for in the future
  -}
  next : Tm (◄ Γ) T → Tm Γ (▻ T)
  next t ⟨ [ zero , _ ] ,  _ ⟩' = tt
  next t ⟨ [ suc m , x ] , γ ⟩' = t ⟨ [ m , x ] , γ ⟩'
  naturality (next t) [ z≤n , _ ] _ = refl
  naturality (next t) [ s≤s m≤n , _ ] _ = naturality t [ m≤n , _ ] _

  {-
    Γ ⊢ t : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
    -----------------------------------      
    ◄ Γ ⊢ prev t : ✲₁ ← ✲₂ ← ✲₃ ... 

    An inverse of the term constructor `next`; access the informaiton next step now
  -}
  prev : Tm Γ (▻ T) → Tm (◄ Γ) T
  prev t ⟨ [ m , x ] , γ ⟩' = t ⟨ [ suc m , x ] , γ ⟩'
  naturality (prev t) [ m≤n , _ ] eγ = naturality t [ s≤s m≤n , _ ] eγ
  
  -- A proof that `prev` is a left inverse of `next`
  prev-next : (t : Tm (◄ Γ) T) → prev (next t) ≅ᵗᵐ t
  eq (prev-next t) _ = refl

  -- A proof that `next` is a left inverse of `prev`
  next-prev : (t : Tm Γ (▻ T)) → next (prev t) ≅ᵗᵐ t
  eq (next-prev t) {[ 0 , _ ]} _ = refl
  eq (next-prev t) {[ suc m , _ ]} _ = refl

{-
  Γ ⊢ t         : ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  --------------------------------------           
  ◄ Γ ⊢ prev' t : ✲₁ ← ✲₂ ← ✲₃ ... 

  Disgards the current informaiton and accesses the informaiton next step now
-}
prev' : {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (T [ from-earlier Γ ])
prev' t = t [ from-earlier _ ]'

{-
  Γ ⊢ t         : ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  --------------------------------------           
  ◄ Γ ⊢ prev' t : ✲₁ ← ✲₂ ← ✲₃ ...
  -------------------------------------
  Γ ⊢ next' t   : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ...

  A term constructor for type `▻' T`
-}
next' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻' T)
next' t = next (prev' t)

{- löb : (▻' T → T) → T
  Γ ⊢ f : ▻' T ⇛ T
  ------------------
  Γ ⊢ löb T f : T

  löb T f = t[x ↦ next (löb T f)] where x : ▻' T is the input variable of f
-}
löb : (T : Ty Γ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
löb {Γ = Γ} T f = MkTm tm natural
  {-
    f ⟨ [ n , y ] , γy ⟩' : PshFun (▻' T) T [ n , y ] γy
      which contains information about what `f ⟨ [ n , y ] γy ⟩' does to each arrow to [ n , y ] γy at ∫Γ
    `tm` is defined recursively
  -}
  where
    tm : (mx : Ob ω×V) (γ : Γ ⟨ mx ⟩) → T ⟨ mx , γ ⟩
    tm [ 0 , x ] γ = f €⟨ [ 0 , x ] , γ ⟩ tt
      {- 
        Γ ⊢ f ⟨ [ 0 , x ] , γ ⟩' : PshFun (▻' T) T [ 0 , x ] γ
        Γ ⊢ f ⟨ [ 0 , x ] , γ ⟩' $⟨ hom-id ω×V , ctx-id Γ ⟩_ : ▻' T ⟨ [ 0 , x ] , γ ⟩ → T ⟨ [ 0 , x ] , γ ⟩
        ---------------------------------------------------------------------------
        Γ ⊢ f €⟨ [ 0 , x ] , γ ⟩_ : ▻' T ⟨ [ 0 , x ] , γ ⟩ → T ⟨ [ 0 , x ] , γ ⟩
                                   = ⊤ → T ⟨ [ 0 , x ] , γ ⟩
      -}
    tm [ suc m , x ] γ = f €⟨ [ suc m , x ] , γ ⟩ tm [ m , x ] (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ γ)
      {- 
        γ : Γ ⟨ [ m+1 , x ] ⟩ = ◄ Γ ⟨ [ m , x ] ⟩
        ▻' T ⟨ [ m+1 , x ] , γ ⟩ = T ⟨ [ m , x ] , Γ ⟪ [ m≤m+1 , hom-id V ] ⟫ γ ⟩
        
        Γ ⊢ f ⟨ [ m+1 , x ] , γ ⟩' : PshFun (▻' T) T [ m+1 , x ] γ
        Γ ⊢ f ⟨ [ m+1 , x ] , γ ⟩' $⟨ hom-id ω×V , ctx-id Γ ⟩_ : ▻' T ⟨ [ m+1 , x ] , γ ⟩ → T ⟨ [ m+1 , x ] , γ ⟩
        ---------------------------------------------------------------------------------------
        Γ ⊢ f €⟨ [ m+1 , x ] , γ ⟩_ : T ⟨ [ m , x ] , Γ ⟪ [ m≤m+1 , hom-id V ] ⟫ γ ⟩ → T ⟨ [ m+1 , x ] , γ ⟩

        `tm [ m , x ] (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ γ)` has type of the domain.
      -}
    open ≡-Reasoning -- 
    natural : ∀ {mx ny : Ob ω×V} {γn : Γ ⟨ ny ⟩} {γm : Γ ⟨ mx ⟩} (m≤n-g : Hom ω×V mx ny) (eγ : Γ ⟪ m≤n-g ⟫ γn ≡ γm) → T ⟪ m≤n-g , eγ ⟫ tm ny γn ≡ tm mx γm
    {-
      {[ m , x ]} {[ n , y ]} {γn} {γm} {m≤n} {g} (eγ : Γ ⟪ [ m≤n , g ] ⟫ γn ≡ γm
      RHS: T ⟪ [ m≤n , g ] , eγ ⟫ _⟨ [ n , y ] , γn ⟩' ≡ _⟨ [ m , x ] , γm ⟩'

      Given
                                              ▻' T ⟪ [ m≤n , g ] , eγ ⟫_
                  ⊤ = ▻' T ⟨ [ m , x ] , γm ⟩ ←------------------------------ ▻' T ⟨ [ n , y ] , γn ⟩ = ⊤ ∋ t
                              |                                                       |
      f €⟨ [ m , x ] , γm ⟩_ |                                                        | f €⟨ [ n , y ] , γn ⟩_
                              ↓                                                       ↓
                    T ⟨ [ m , x ] , γm ⟩ ←------------------------------ T ⟨ [ n , y ] , γn ⟩ 
                                                T ⟪ [ m≤n , g ] , eγ ⟫_
    -}
    natural {mx = [ 0 , x ]} {ny = [ 0 , y ]} [ z≤n {0} , g ] eγ = €-natural f
      {-
        RHS: 
          T ⟪ [ z≤n {0} , g ] , eγ ⟫ tm [ 0 , y ] γn ≡ tm [ 0 , x ] γm
        = T ⟪ [ z≤n {0} , g ] , eγ ⟫ (f €⟨ [ 0 , y ] , γn ⟩ tt) ≡ f €⟨ [ 0 , x ] , γx ⟩ tt
        = T ⟪ [ z≤n {0} , g ] , eγ ⟫ (f €⟨ [ 0 , y ] , γn ⟩ tt) ≡ f €⟨ [ 0 , x ] , γx ⟩ (▻' T ⟪ [ z≤n , g ] , eγ ⟫ tt)

                                                 ▻' T ⟪ [ 0≤n , g ] , eγ ⟫_
                     ▻' T ⟨ [ 0 , x ] , γm ⟩ ←------------------------------ ▻' T ⟨ [ 0 , y ] , γn ⟩ ∋ .tt
                                |                                                    |
        f €⟨ [ 0 , y ] , γn ⟩_ |                                                     | f €⟨ [ 0 , y ] , γn ⟩_
                               ↓                                                     ↓
                      T ⟨ [ 0 , x ] , γm ⟩ ←------------------------------ T ⟨ [ 0 , y ] , γn ⟩ 
                                                 T ⟪ [ m≤n , g ] , eγ ⟫_


      -}
    natural {mx = [ 0 , x ]} {ny = [ suc n , y ]} [ z≤n {suc n} , g ] eγ = €-natural f
      {-
        RHS: 
          T ⟪ [ 0≤n+1 , g ] , eγ ⟫ f €⟨ [ n+1 , y ] , γn ⟩ _⟨ [ n , y ] , (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ γn ⟩' ≡ f €⟨ [ 0 , x ] , γm ⟩ tt
                                                    ? ↦ tt
                                ⊤ ←-------------------------------------- T ⟨ [ n , y ] , γn ⟩
                                |                                                    |
        f €⟨ [ 0 , x ] , γm ⟩_ |                                                     | f €⟨ [ n+1 , y ] , γn ⟩_
                               ↓                                                     ↓
                      T ⟨ [ 0 , x ] , γm ⟩ ←------------------------------ T ⟨ [ n+1 , y ] , γn ⟩ 
                                                  T ⟪ [ 0≤n+1 , g ] , eγ ⟫_
      -}
    natural {mx = [ suc m , x ]} {ny = [ suc n , y ]} {γn} {γm} [ s≤s m≤n , g ] eγ = 
      {-
        RHS: T ⟪ [ m+1≤n+1 , g ] , eγ ⟫ _⟨ [ n+1 , y ] , γn ⟩' ≡ _⟨ [ m+1 , x ] , γm ⟩'
        = T ⟪ [ m+1≤n+1 , g ] , eγ ⟫ (f €⟨ [ n+1 , y ] , γn ⟩ (_⟨ [ n , y ] , Γ ⟪ [ n≤n+1 , hom-id V {y} ] ⟫ γn)) ≡ f €⟨ [ m+1 , x ] , γm ⟩ (_⟨ [ m , x ] , Γ ⟪ m≤m+1 ⟫ γm ⟩) 

                                                          T ⟪ [ m≤n , g ] , new-proof ⟫_
                  ▻' T ⟨ [ m+1 , x ] , Γ ⟪ m≤m+1 ⟫ γm ⟩ ←------------------------------ T ⟨ [ n , y ] , Γ ⟪ n≤n+1 ⟫ γn ⟩ ∋ tm [ n , y ] Γ ⟪ [ n≤n+1 , hom-id V {y} ] ⟫ γn
                                |                                                                    |
        f €⟨ [ m+1 , x ] , γm ⟩_ |                                                                     | f €⟨ [ n+1 , y ] , γn ⟩_
                                  ↓                                                                    ↓
                      T ⟨ [ m+1 , x ] , γm ⟩ ←------------------------------------------ T ⟨ [ n+1 , y ] , γn ⟩ 
                                                      T ⟪ [ m+1≤n+1 , g ] , eγ ⟫_
      -}
      begin
        T ⟪ [ s≤s m≤n , g ] , eγ ⟫ tm [ suc n , y ] γn
      ≡⟨⟩
        T ⟪ [ s≤s m≤n , g ] , eγ ⟫ (f €⟨ [ suc n , y ] , γn ⟩ (tm [ n , y ] (Γ ⟪ [ n≤1+n n , hom-id V ] ⟫ γn)))
      ≡⟨ €-natural f ⟩
        f €⟨ [ suc m , x ] , γm ⟩ (T ⟪ [ m≤n , g ] , _ ⟫ (tm [ n , y ] (Γ ⟪ [ n≤1+n n , hom-id V {y} ] ⟫ γn)))
      ≡⟨ cong (f €⟨ _ , _ ⟩_) (natural [ m≤n , g ] _) ⟩
        f €⟨ [ suc m , x ] , γm ⟩ (tm [ m , x ] (Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ γm)) ∎

{- todo: Understand
  Γ ⊢ T 
  Γ, [ m , x ] : ▻' T ⊢ T [ π ] ⟨ [ m , x ] , [ γ , t ] ⟩ = T ⟨ [ m , x ] , γ ⟩

  Γ ⊢ T type
  Γ, _ : ▻' T ⊢ f : T [ π ]
                f ⟨ [ m , x ] , [ γ , t ] ⟩' : T ⟨ [ m , x ] , γ ⟩
    where γ : Γ ⟨ [ m , x ] ⟩ and t :  ▻' T ⟨ [ m , x ] , γ ⟩
  -----------------------------
  Γ ⊢ lam (▻' T) f : ▻' T ⇛ T
  -----------------------------------------
  Γ ⊢ löb' T f = löb T (lam (▻' T) f) : T

  löb vs. löb'
    > the former requires as an input a funciton that looks like λx.t
    > the latter requires only the body t
  without a named variable
-}
löb' : (T : Ty Γ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
löb' T f = löb T (lam (▻' T) f)

-- with a named variable
löb[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻' T) (T [ π ]) → Tm Γ T
löb[_∈▻'_]_ v = löb'

{-
  Γ ⊢ T type
  Γ ⊢ f : ▻' T ⇛ T
      f ⟨ [ m , x ] , γ ⟩' : (▻' T ⇛ T) ⟨ [ m , x ] , γ ⟩ = PshFun (▻' T) T [ m , x ] γ

  Γ ⊢ löb T f : ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ next' (löb T f) : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ...
  ---------------------------------------
  Γ ⊢ app f (next' (löb T f)) = löb T f
  
  A proof that `löb` produces a fix point of any given function of type ▻' T ⇛ T; that is,  `fix f = f (fix f)` holds when `fix` is replaced by `löb`.
-}
löb-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) →
                  app f (next' (löb T f)) ≅ᵗᵐ löb T f
eq (löb-is-fixpoint f) {[ 0 , _ ]} γ = refl
  {-
    {[ 0 , x ]} {γ : Γ ⟨ [ 0 , x ] ⟩}
    RHS: 
      app f (next' (löb T f)) ⟨ [ 0 , x ] , γ ⟩' ≡ löb T f ⟨ [ 0 , x ] , γ ⟩'

      app f (next' (löb T f)) ⟨ [ 0 , x ] , γ ⟩'
    = f €⟨ [ 0 , x ] , γ ⟩ ((next ((löb T f) [ from-earlier _ ]')) ⟨ [ 0 , x ] , γ ⟩')
    = f €⟨ [ 0 , x ] , γ ⟩ tt 
    = löb T f ⟨ [ 0 , x ] , γ ⟩'
  -}
eq (löb-is-fixpoint f) {[ suc n , _ ]} γ = refl
  {-
    {[ m+1 , x ]} {γ : Γ ⟨ [ m+1 , x ] ⟩}
    RHS: 
      app f (next' (löb T f)) ⟨ [ m+1 , x ] , γ ⟩' ≡ löb T f ⟨ [ m+1 , x ] , γ ⟩'

      app f (next' (löb T f)) ⟨ [ 0 , x ] , γ ⟩'
    = f €⟨ [ m+1 , x ] , γ ⟩ ((next ((löb T f) [ from-earlier _ ]')) ⟨ [ m+1 , x ] , γ ⟩')
    = f €⟨ [ m+1 , x ] , γ ⟩ (((löb T f) [ from-earlier _ ]') ⟨ [ m , x ] , γ ⟩')
    = f €⟨ [ m+1 , x ] , γ ⟩ ((löb T f) ⟨ [ m , x ] , func (from-earlier _) γ ⟩')
    = f €⟨ [ m+1 , x ] , γ ⟩ ((löb T f) ⟨ [ m , x ] , Γ ⟪ m≤m+1 ⟫ γ ⟩')
    = (löb T f) ⟨ [ m+1 , x ] , γ ⟩'
  -}

-- If both t and s are fix points of a given function f, then they are equivalent.
fixpoint-unique : {T : Ty Γ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
                  app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
eq (fixpoint-unique f t s t-fix s-fix) {x = [ 0 , x ]}  γ = 
  begin
    t ⟨ [ 0 , x ] , γ ⟩'
  ≡˘⟨ eq t-fix γ ⟩ 
    f €⟨ [ 0 , x ] , γ ⟩ tt
  ≡⟨ eq s-fix γ ⟩
    s ⟨ [ 0 , x ] , γ ⟩' ∎
  where open ≡-Reasoning
eq (fixpoint-unique f t s t-fix s-fix) {x = [ suc n , x ]} γ =
  begin
    t ⟨ [ suc n , x ] , γ ⟩'
  ≡˘⟨ eq t-fix γ ⟩
    f €⟨ [ suc n , x ] , γ ⟩ (t ⟨ [ n , x ] , _ ⟩')
  ≡⟨ cong (f €⟨ [ suc n , x ] , γ ⟩_) (eq (fixpoint-unique f t s t-fix s-fix) {x = [ n , x ]}  _) ⟩
    f €⟨ [ suc n , x ] , γ ⟩ (s ⟨ [ n , x ] , _ ⟩')
  ≡⟨ eq s-fix γ ⟩
    s ⟨ [ suc n , x ] , γ ⟩' ∎
  where open ≡-Reasoning

{-
  ◄ Γ ⊢ T S = ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ T ⇛ S : ✲₁ ← ✲₂ ← ✲₃ ... 
                                 ↓
                ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ f : ▻ (T ⇛ S) = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
                                            ↓
                       ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 

  Γ ⊢ t : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ prev t : ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ app f (prev t) : ✪₁ ← ✪₂ ← ✪₃ ... 
  --------------------------------------------------------------
  Γ ⊢ f ⟨$⟩ t = next (app f (prev t)) : ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 

  ▻ is an applicative functor as in ◄ Γ ⊢ f : T ⇛ S is a map Γ ⊢ ▻ T → ▻ S.
-}
_⟨$⟩_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⟨$⟩ t = next (app f (prev t))

{-
  ◄ Γ ⊢ T S : ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ f : ▻ (T ⇛ S) = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
                                            ↓
                       ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
  ◄ Γ ⊢ prev f : T ⇛ S = ✲₁ ← ✲₂ ← ✲₃ ... 
                                          ↓
                          ✪₁ ← ✪₂ ← ✪₃ ... 
  ------------------------------------------------------
  Γ ⊢ f ⊛ t = (prev f) ⟨$⟩ t : ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
-}
_⊛_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⊛ t = prev f ⟨$⟩ t


--------------------------------------------------
-- Congruence and naturality for the later modality

{-
  ◄ Γ ⊢ η : T ↣ T' = ✲₁ ← ✲₂ ← ✲₃ ... 
                      ↓    ↓     ↓ 
                      ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ (▻ T) (▻ T') = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  ---------------------------------------------------
  Γ ⊢ ▻-map η : ▻ T ↣ ▻ T' = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
                               ↓    ↓     ↓    ↓
                              ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
-}
▻-map : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} → (T ↣ T') → (▻ T ↣ ▻ T')
func (▻-map η) {[ 0 , _ ]} .tt = tt
  {-
    RHS: 
      ▻ T ⟨ [ 0 , x ] , γ ⟩ → ▻ T' ⟨ [ 0 , x ] , γ ⟩
    = ⊤ → ⊤
  -}
func (▻-map η) {[ suc m , x ]} {γ} t = func η {[ m , x ]} {γ} t
  {-
    RHS: 
      ▻ T ⟨ [ m+1 , x ] , γ ⟩ → ▻ T' ⟨ [ m+1 , x ] , γ ⟩
    = T ⟨ [ m , x ] , γ ⟩ → T' ⟨ [ m , x ] , γ ⟩
    = func η {[ m , x ]} {γ}
  -}
naturality (▻-map η) {f = [ z≤n , g ]} = refl
  {-
    {[ 0 , x ]} {[ n , y ]} {[ 0≤n , g ]} {γy = γn} {γx = γm} {eγ} {t : T ⟨ [ n , y ] , γn ⟩} 
                                      ▻ T ⟪ [ 0≤n , g ] , eγ ⟫_
         ▻ T' ⟨ [ 0 , x ] , γm ⟩ ←--------------------- ▻ T' ⟨ [ n , y ] , γn ⟩
                   ↑                                               ↑
    func (▻-map η) |                                               | func (▻-map η)
                   |                                               |
         ▻ T ⟨ [ 0 , x ] , γm ⟩ ←--------------------- ▻ T ⟨ [ n , y ] , γn ⟩ ∋ t
                                 ▻ T ⟪ [ 0≤n , g ] , eγ ⟫_
      ▻ T ⟪ [ 0≤n , g ] , eγ ⟫ (func (▻-map η) {[ n , y ]} {γn} t)
    = ▻ T ⟪ [ 0≤n , g ] , eγ ⟫ (func η {[ n-1 , x ]} {γn} t)
    = tt
      func (▻-map η) {[ 0 , x ]} {γm} (▻ T ⟪ [ 0≤n , g ] , eγ ⟫ t) = tt
  -}
naturality (▻-map η) {f = [ s≤s m≤n , g ]} = naturality η

{-
  Γ ⊢ T = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ S = ✪₀ ← ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ η : T ↣ S : ✲₀ ← ✲₁ ← ✲₂ ... 
                   ↓     ↓    ↓
                  ✪₀ ← ✪₁ ← ✪₂ ... 
  ◄ Γ ⊢ ty-subst-map (from-earlier Γ) η : T [ from-earlier Γ ] ↣ S [ from-earlier Γ ]
                                         = ✲₁ ← ✲₂ ← ✲₃ ... 
                                            ↓    ↓    ↓ 
                                           ✪₁ ← ✪₂ ← ✪₃ ... 
  ------------------------------------------
  Γ ⊢ ▻-map (ty-subst-map (from-earlier _) η) : ▻' T ↣ ▻' S = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
                                                                ↓    ↓     ↓    ↓
                                                               ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
-}
▻'-map : {T : Ty Γ} {S : Ty Γ} → (T ↣ S) → (▻' T ↣ ▻' S)
▻'-map η = ▻-map (ty-subst-map (from-earlier _) η)

{- skipped: all the actual proofs from this point
  ◄ Γ ⊢ T = ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ T' = ✪₁ ← ✪₂ ← ✪₃ ... 
  ◄ Γ ⊢ T ≅ᵗʸ T' 
  ------------------------------------
  Γ ⊢ ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ ▻ T' = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ ▻ T ≅ᵗʸ ▻ T'

  ▻ respects equivalence of types.
-}
▻-cong : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} → T ≅ᵗʸ T' → ▻ T ≅ᵗʸ ▻ T'
from (▻-cong T=T') = ▻-map (from T=T')
to (▻-cong T=T') = ▻-map (to T=T')
eq (isoˡ (▻-cong T=T')) {[ 0 , _ ]} _ = refl
eq (isoˡ (▻-cong T=T')) {[ suc n , _ ]} = eq (isoˡ T=T')
eq (isoʳ (▻-cong T=T')) {[ 0 , _ ]} _ = refl
eq (isoʳ (▻-cong T=T')) {[ suc n , _ ]} = eq (isoʳ T=T')

{-
  Γ ⊢ T = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ T' = ✪₀ ← ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ T ≅ᵗʸ T'
  ---------------
  Γ ⊢ ▻' T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ ▻' T' = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ ▻' T ≅ᵗʸ ▻' T'

  ▻' respects equivalence of types.
-}
▻'-cong : {T : Ty Γ} {T' : Ty Γ} → T ≅ᵗʸ T' → ▻' T ≅ᵗʸ ▻' T'
▻'-cong {Γ = Γ} T=T' = ▻-cong (ty-subst-cong-ty (from-earlier Γ) T=T')

{-
  ◄ Γ ⊢ t t' : T = ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ t ≅ᵗᵐ t'
  -----------------------------------
  Γ ⊢ next t next t' : ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ next t ≅ᵗᵐ next t'

  `next` respects equivalence of terms.
-}
next-cong : {T : Ty (◄ Γ)} {t t' : Tm (◄ Γ) T} → t ≅ᵗᵐ t' → next t ≅ᵗᵐ next t'
eq (next-cong t=t') {[ 0 , _ ]} _ = refl
eq (next-cong t=t') {[ suc m , _ ]} = eq t=t'

{-
  ◄ Γ ⊢ T = ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ t ≅ᵗᵐ t' : ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  --------------------------------
  ◄ Γ ⊢ prev t ≅ᵗᵐ prev t' : ✲₁ ← ✲₂ ← ✲₃ ... 

  `prev` respects equivalence of terms. 
-}
prev-cong : {T : Ty (◄ Γ)} {t t' : Tm Γ (▻ T)} → t ≅ᵗᵐ t' → prev t ≅ᵗᵐ prev t'
eq (prev-cong t=t') = eq t=t'

{-
  Γ ⊢ T = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ f ≅ᵗᵐ f' : ▻' T ⇛ T
                = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
                                        ↓
                  ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ löb T f ≅ᵗᵐ löb T f' : ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 

  `löb` respects equivalence of functions.
-}
löb-cong : (T : Ty Γ) {f f' : Tm Γ (▻' T ⇛ T)} → f ≅ᵗᵐ f' → löb T f ≅ᵗᵐ löb T f'
eq (löb-cong T f=f') {[ 0 , _ ]} γ = cong (_$⟨ [ z≤n , hom-id V ] , _ ⟩ tt) (eq f=f' γ)
eq (löb-cong T f=f') {[ suc m , _ ]} _ = €-cong f=f' (eq (löb-cong T f=f') {[ m , _ ]} _)

{-
  ◄ Γ ⊢ T = ✲₁ ← ✲₂ ← ✲₃ ... 
  ◄ Γ ⊢ T' = ✪₁ ← ✪₂ ← ✪₃ ... 
  ◄ Γ ⊢ T ≅ᵗʸ T' (by T=T')
-}
module _ {Γ : Ctx ω×V} {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} (T=T' : T ≅ᵗʸ T') where
  {-
    Γ ⊢ ▻ T ≅ᵗʸ ▻ T' (by ▻-cong T=T')
    ◄ Γ ⊢ t : T' = ✪₁ ← ✪₂ ← ✪₃ ... 
    Γ ⊢ next t : ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
    ------------------------------------------------------
    Γ ⊢ ι[ ▻-cong T=T' ] next t : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 

    ◄ Γ ⊢ t : T' = ✪₁ ← ✪₂ ← ✪₃ ... 
    ◄ Γ ⊢ T ≅ᵗʸ T' (by T=T')
    ---------------------------------------
    ◄ Γ ⊢ ι[ T=T' ] t : ✲₁ ← ✲₂ ← ✲₃ ...
    Γ ⊢ next (ι[ T=T' ] t) : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
    ----------------------------------------------------
    Γ ⊢ ι[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι[ T=T' ] t) 

    `next` commutes with change of typing judgements.
  -}
  next-ι : (t : Tm (◄ Γ) T') → ι[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι[ T=T' ] t)
  eq (next-ι t) {[ 0 , _ ]}  _ = refl
  eq (next-ι t) {[ suc m , _ ]} _ = refl
  
  {-
    Γ ⊢ t : ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
    ◄ Γ ⊢ prev t : ✪₁ ← ✪₂ ← ✪₃ ... 
    ◄ Γ ⊢ T ≅ᵗʸ T' (by T=T')
    ----------------------------------------------
    ◄ Γ ⊢ ι[ T=T' ] (prev t) : ✲₁ ← ✲₂ ← ✲₃ ...

    Γ ⊢ ▻ T ≅ᵗʸ ▻ T' (by ▻-cong T=T')
    Γ ⊢ ι[ ▻-cong T=T' ] t : ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
    -----------------------------------------------------
    ◄ Γ ⊢ prev (ι[ ▻-cong T=T' ] t) : ✲₁ ← ✲₂ ← ✲₃ ... 
    ◄ Γ ⊢ ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)

    `prev` commutes with change of typing judgements.
  -}
  prev-ι : (t : Tm Γ (▻ T')) → ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)
  eq (prev-ι t) _ = refl

{-
  Γ ⊢ T = ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ T' = ✪₀ ← ✪₁ ← ✪₂ ← ✪₃ ... 
  Γ ⊢ T ≅ᵗʸ T' (by T=T')
  Γ ⊢ f : ▻' T' ⇛ T'
        = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... 
                                ↓
          ✪₀ ← ✪₁ ← ✪₂ ← ✪₃ ...
  Γ ⊢ löb T' f : ✪₀ ← ✪₁ ← ✪₂ ← ✪₃ ...
  ---------------------------------------------------
  Γ ⊢ ι[ T=T' ] (löb T' f) : ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ ▻ T ≅ᵗʸ ▻ T' (by ▻-cong T=T')
  Γ ⊢ (▻' T ⇛ T) ≅ᵗʸ (▻' T' ⇛ T') (by ⇛-cong (▻'-cong T=T') T=T')
  ---------------------------------------------------
  Γ ⊢ ι[ ⇛-cong (▻'-cong T=T') T=T' ] f : ▻' T ⇛ T
                                         = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
                                                                ↓ 
                                           ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 
  Γ ⊢ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f) : ✲₀ ← ✲₁ ← ✲₂ ← ✲₃ ... 

  `löb` commutes with change of typing judgements.
-}
löb-ι : {T : Ty Γ} {T' : Ty Γ} (T=T' : T ≅ᵗʸ T') (f : Tm Γ (▻' T' ⇛ T')) →
        ι[ T=T' ] (löb T' f) ≅ᵗᵐ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f)
eq (löb-ι T=T' f) {[ 0 , _ ]} _ = refl
eq (löb-ι {Γ = Γ} {T = T} {T' = T'} T=T' f) {[ suc m , _ ]} γ = cong (func (to T=T')) (€-cong (≅ᵗᵐ-refl {t = f}) (
  begin
    löb T' f ⟨ [ m , _ ] , _ ⟩'
  ≡˘⟨ eq (isoʳ T=T') _ ⟩
    func (from T=T') (func (to T=T') (löb T' f ⟨ [ m , _ ] , _ ⟩'))
  ≡⟨ cong (func (from T=T')) (eq (löb-ι T=T' f) {[ m , _ ]} _) ⟩
    func (from T=T') (löb T g ⟨ [ m , _ ] , _ ⟩') ∎))
  where
    open ≡-Reasoning
    g : Tm Γ (▻' T ⇛ T)
    g = ι[ ⇛-cong (▻'-cong T=T') T=T' ] f
{-
  ◄ Γ ⊢T = ✲₁ ← ✲₂ ← ✲₃ ... 
-}
module _ {Δ : Ctx ω×V} {Γ : Ctx ω×V} (σ : Δ ⇒ Γ) {T : Ty (◄ Γ)} where
  {-
    ◄ Γ ⊢ T = ✲₁ ← ✲₂ ← ✲₃ ... 
    Γ ⊢ ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ... 
    ----------------------------------
    Δ ⊢ (▻ T) [ σ ] = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... ------------
                                                          |
    ◄ Δ ⊢ T [ ◄-subst σ ] = ✪₁ ← ✪₂ ← ✪₃ ...           |
    Δ ⊢ ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... ←--|
  -}
  ▻-natural-from : (▻ T) [ σ ] ↣ ▻ (T [ ◄-subst σ ])
  func ▻-natural-from {[ 0 , _ ]} t = t
  func ▻-natural-from {[ suc m , _ ]} t = t
  naturality ▻-natural-from {f = [ z≤n , _ ]} = refl
  naturality ▻-natural-from {f = [ s≤s m≤n , _ ]} = refl
  {-
    ◄ Δ ⊢ T [ ◄-subst σ ] = ✪₁ ← ✪₂ ← ✪₃ ...           
    Δ ⊢ ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... --
                                                        |
    ◄ Γ ⊢ T = ✲₁ ← ✲₂ ← ✲₃ ...                        |
    Γ ⊢ ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ...                   |
    ------------------------------------------          |
    Δ ⊢ (▻ T) [ σ ] = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ... ←--------|

  -}
  ▻-natural-to : ▻ (T [ ◄-subst σ ]) ↣ (▻ T) [ σ ]
  func ▻-natural-to {[ 0 , _ ]} t = t
  func ▻-natural-to {[ suc m , _ ]} t = t
  naturality ▻-natural-to {f = [ z≤n , _ ]} = refl
  naturality ▻-natural-to {f = [ s≤s m≤n , _ ]} = refl
  
  -- Δ ⊢ (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...
  ▻-natural : (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ])
  from ▻-natural = ▻-natural-from
  to ▻-natural = ▻-natural-to
  eq (isoˡ ▻-natural) {[ 0 , _ ]}  _ = refl
  eq (isoˡ ▻-natural) {[ suc m , _ ]} _ = refl
  eq (isoʳ ▻-natural) {[ 0 , _ ]}  _ = refl
  eq (isoʳ ▻-natural) {[ suc m , _ ]} _ = refl

  {-
    ◄ Γ ⊢ t : T = ✲₁ ← ✲₂ ← ✲₃ ... 
    Γ ⊢ next t : ▻ T = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ...
    ----------------------------------------------------------
    Δ ⊢ (next t) [ σ ]' : (▻ T) [ σ ] = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...

    ◄ Δ ⊢ t [ ◄-subst σ ]' : T [ ◄-subst σ ] = ✪₁ ← ✪₂ ← ✪₃ ...
    Δ ⊢ next (t [ ◄-subst σ ]') : ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...
    Δ ⊢ (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...
    -------------------------------------------------------------------------------------
    Δ ⊢ ι[ ▻-natural ] (next (t [ ◄-subst σ ]')) : (▻ T) [ σ ] = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...

    `next` commutes with change of term type judgement.
  -}
  next-natural : (t : Tm (◄ Γ) T) → (next t) [ σ ]' ≅ᵗᵐ ι[ ▻-natural ] (next (t [ ◄-subst σ ]'))
  eq (next-natural t) {[ 0 , _ ]} _ = refl
  eq (next-natural t) {[ suc m , _ ]} _ = refl
  
  {-
    Γ ⊢ t : ▻ T      = ⊤ ← ✲₁ ← ✲₂ ← ✲₃ ...
    ◄ Γ ⊢ prev t : T = ✲₁ ← ✲₂ ← ✲₃ ...
    ---------------------------------------------------
    ◄ Δ ⊢ (prev t) [ ◄-subst σ ]' : ✪₁ ← ✪₂ ← ✪₃ ...

    Δ ⊢ t [ σ ]' : ▻ T [ σ ] = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...
    Δ ⊢ (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...
    ---------------------------------------------------------------------------------
    Δ ⊢ ι⁻¹[ ▻-natural ] (t [ σ ]') : ▻ (T [ ◄-subst σ ]) = ⊤ ← ✪₁ ← ✪₂ ← ✪₃ ...
    ◄ Δ ⊢ prev (ι⁻¹[ ▻-natural ] (t [ σ ]')) : T [ ◄-subst σ ] = ✪₁ ← ✪₂ ← ✪₃ ...

    `prev` commutes with change of term type judgement.
  -}
  prev-natural : (t : Tm Γ (▻ T)) → (prev t) [ ◄-subst σ ]' ≅ᵗᵐ prev (ι⁻¹[ ▻-natural ] (t [ σ ]'))
  eq (prev-natural t) _ = refl

-- todo: START HERE
module _ {Δ : Ctx ω×V} {Γ : Ctx ω×V} (σ : Δ ⇒ Γ) {T : Ty Γ} where
  ▻'-natural : (▻' T) [ σ ] ≅ᵗʸ ▻' (T [ σ ])
  ▻'-natural =
    begin
      ▻ (T [ from-earlier Γ ]) [ σ ]
    ≅⟨ ▻-natural σ ⟩
      ▻ (T [ from-earlier Γ ] [ ◄-subst σ ])
    ≅⟨ ▻-cong (ty-subst-seq-cong (from-earlier Γ ∷ ◄-subst σ ◼) (σ ∷ (from-earlier Δ ◼)) T (from-earlier-natural σ)) ⟩
      ▻ (T [ σ ] [ from-earlier Δ ]) ∎
    where open ≅ᵗʸ-Reasoning

  löb-natural : (f : Tm Γ (▻' T ⇛ T)) →
                (löb T f) [ σ ]' ≅ᵗᵐ löb (T [ σ ]) (ι⁻¹[ ⇛-cong ▻'-natural ≅ᵗʸ-refl ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]')))
  eq (löb-natural f) {[ 0 , _ ]} δ = $-cong (f ⟨ [ 0 , _ ] , func σ δ ⟩') refl
  eq (löb-natural f) {[ suc m , _ ]} δ =
    begin
      f ⟨ [ suc m , _ ] , func σ δ ⟩' $⟨ [ s≤s ≤-refl , hom-id V ] , ctx-id Γ ⟩ (löb T f ⟨ [ m , _ ] , Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ (func σ δ) ⟩')
    ≡⟨ $-cong (f ⟨ [ suc m , _ ] , func σ δ ⟩') refl ⟩
      f ⟨ [ suc m , _ ] , func σ δ ⟩' $⟨ [ s≤s ≤-refl , hom-id V ] , α ⟩ (löb T f ⟨ [ m , _ ] , Γ ⟪ [ n≤1+n m , hom-id V ] ⟫ (func σ δ) ⟩')
    ≡˘⟨ cong (f ⟨ [ suc m , _ ] , func σ δ ⟩' $⟨ [ s≤s ≤-refl , hom-id V ] , α ⟩_) (naturality (löb T f) [ ≤-refl , hom-id V ] β) ⟩
      f ⟨ [ suc m , _ ] , func σ δ ⟩' $⟨ [ s≤s ≤-refl , hom-id V ] , α ⟩ (T ⟪ [ ≤-refl , hom-id V ] , β ⟫ ((löb T f) [ σ ]' ⟨ [ m , _ ] , Δ ⟪ [ n≤1+n m , hom-id V ] ⟫ δ ⟩'))
    ≡⟨ cong (f ⟨ [ suc m , _ ] , func σ δ ⟩' $⟨ [ s≤s ≤-refl , hom-id V ] , α ⟩_ ∘ T ⟪ [ ≤-refl , hom-id V ] , β ⟫_) (eq (löb-natural f) {[ m , _ ]} (Δ ⟪ [ n≤1+n m , hom-id V ] ⟫ δ)) ⟩
      f ⟨ [ suc m , _ ] , func σ δ ⟩' $⟨ [ s≤s ≤-refl , hom-id V ] , α ⟩ (T ⟪ [ ≤-refl , hom-id V ] , β ⟫ (löb (T [ σ ]) g ⟨ [ m , _ ] , Δ ⟪ [ n≤1+n m , hom-id V ] ⟫ δ ⟩')) ∎
    where
      open ≡-Reasoning
      α = _
      β = _
      g : Tm Δ (▻' (T [ σ ]) ⇛ (T [ σ ]))
      g = ι⁻¹[ ⇛-cong ▻'-natural ≅ᵗʸ-refl ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]'))

instance
  ▻'-closed : {A : ClosedTy ω×V} {{_ : IsClosedNatural A}} → IsClosedNatural (▻' A)
  closed-natural {{▻'-closed}} σ = ≅ᵗʸ-trans (▻'-natural σ) (▻'-cong (closed-natural σ))

  ▻-closed : {A : ClosedTy ω×V} {{_ : IsClosedNatural A}} → IsClosedNatural (▻ A)
  closed-natural {{▻-closed}} σ = ≅ᵗʸ-trans (▻-natural σ) (▻-cong (closed-natural (◄-subst σ)))

-- ▻' is an applicative functor as well (but this requires ▻-cong).
module _ {T : Ty Γ} {S : Ty Γ} where
  infixl 12 _⊛'_
  infixl 12 _⟨$⟩'_

  _⊛'_ : Tm Γ (▻' (T ⇛ S)) → Tm Γ (▻' T) → Tm Γ (▻' S)
  f ⊛' t = (ι⁻¹[ ▻-cong (⇛-natural _) ] f) ⊛ t

  _⟨$⟩'_ : Tm Γ (T ⇛ S) → Tm Γ (▻' T) → Tm Γ (▻' S)
  f ⟨$⟩' t = next' f ⊛' t

-- The following operations would be easier to define for closed types (since we can then make use of
-- lamι, varι, ⟨$⟩ and ⊛) but we want them to work for all types.
lift▻ : {T S : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T ⇛ ▻ S)
lift▻ {T = T} f = lam (▻ T) (
  ι[ ▻-natural π ] next (
  ι⁻¹[ ⇛-natural (◄-subst π) ] (f [ ◄-subst π ]') $ prev (ι⁻¹[ ▻-natural π ] ξ)))

lift2▻ : {T S R : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S ⇛ R) → Tm Γ (▻ T ⇛ ▻ S ⇛ ▻ R)
lift2▻ {T = T}{S} f = lam (▻ T) (ι[ ⇛-natural π ] ι[ ⇛-cong (▻-natural π) (▻-natural π) ]
  lift▻ (ι⁻¹[ ⇛-natural (◄-subst π) ] (
  ι⁻¹[ ⇛-natural (◄-subst π) ] (f [ ◄-subst π ]') $ prev (ι⁻¹[ ▻-natural π ] ξ))))

lift▻' : {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ (▻' T ⇛ ▻' S)
lift▻' {Γ = Γ} f = lift▻ (ι⁻¹[ ⇛-natural (from-earlier Γ) ] (f [ from-earlier Γ ]'))

lift2▻' : {T S R : Ty Γ} → Tm Γ (T ⇛ S ⇛ R) → Tm Γ (▻' T ⇛ ▻' S ⇛ ▻' R)
lift2▻' {Γ = Γ} f =
  lift2▻ (ι⁻¹[ ⇛-cong ≅ᵗʸ-refl (⇛-natural (from-earlier Γ)) ] ι⁻¹[ ⇛-natural (from-earlier Γ) ] (f [ from-earlier Γ ]'))


--------------------------------------------------
-- Proofs that ▻ and ▻' act functorially on types

▻-map-cong : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} {η φ : T ↣ T'} →
              η ≅ⁿ φ → ▻-map η ≅ⁿ ▻-map φ
eq (▻-map-cong e) {x = [ 0 , _ ]} _ = refl
eq (▻-map-cong e) {x = [ suc m , _ ]} = eq e

▻'-map-cong : {T : Ty Γ} {S : Ty Γ} {η φ : T ↣ S} →
               η ≅ⁿ φ → ▻'-map η ≅ⁿ ▻'-map φ
▻'-map-cong e = ▻-map-cong (ty-subst-map-cong e)

▻-map-id : {T : Ty (◄ Γ)} → ▻-map (id-trans T) ≅ⁿ id-trans (▻ T)
eq ▻-map-id {x = [ 0 , _ ]} _ = refl
eq ▻-map-id {x = [ suc m , _ ]} _ = refl

▻'-map-id : {T : Ty Γ} → ▻'-map (id-trans T) ≅ⁿ id-trans (▻' T)
▻'-map-id {T = T} =
  begin
    ▻-map (ty-subst-map (from-earlier _) (id-trans T))
  ≅⟨ ▻-map-cong (ty-subst-map-id (from-earlier _)) ⟩
    ▻-map (id-trans (T [ from-earlier _ ]))
  ≅⟨ ▻-map-id ⟩
    id-trans (▻' T) ∎
  where open ≅ⁿ-Reasoning

▻-map-comp : {R : Ty (◄ Γ)} {S : Ty (◄ Γ)} {T : Ty (◄ Γ)}
              (η : S ↣ T) (φ : R ↣ S) →
              ▻-map (η ⊙ φ) ≅ⁿ ▻-map η ⊙ ▻-map φ
eq (▻-map-comp η φ) {x = [ 0 , _ ]} _ = refl
eq (▻-map-comp η φ) {x = [ suc m , _ ]} _ = refl

▻'-map-comp : {R : Ty Γ} {S : Ty Γ} {T : Ty Γ}
               (η : S ↣ T) (φ : R ↣ S) →
               ▻'-map (η ⊙ φ) ≅ⁿ ▻'-map η ⊙ ▻'-map φ
▻'-map-comp η φ =
  begin
    ▻'-map (η ⊙ φ)
  ≅⟨⟩
    ▻-map (ty-subst-map (from-earlier _) (η ⊙ φ))
  ≅⟨ ▻-map-cong (ty-subst-map-comp (from-earlier _) η φ) ⟩
    ▻-map (ty-subst-map (from-earlier _) η ⊙ ty-subst-map (from-earlier _) φ)
  ≅⟨ ▻-map-comp _ _ ⟩
    ▻'-map η ⊙ ▻'-map φ ∎
  where open ≅ⁿ-Reasoning

◄-▻-,, : (Γ : Ctx ω×V) (T : Ty (◄ Γ)) → ◄ (Γ ,, ▻ T) ≅ᶜ ◄ Γ ,, T
func (from (◄-▻-,, Γ T)) γt = γt
naturality (from (◄-▻-,, Γ T)) = refl
func (to (◄-▻-,, Γ T)) γt = γt
naturality (to (◄-▻-,, Γ T)) = refl
eq (isoˡ (◄-▻-,, Γ T)) γt = refl
eq (isoʳ (◄-▻-,, Γ T)) γt = refl
