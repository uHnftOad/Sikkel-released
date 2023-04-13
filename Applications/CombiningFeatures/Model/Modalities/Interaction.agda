--------------------------------------------------
-- Proofs about the interactions between the different
--  modalities for guarded recursion
--------------------------------------------------

open import Model.BaseCategory

module Applications.CombiningFeatures.Model.Modalities.Interaction (V : BaseCategory) where

open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit
open import Function using (id; _∘_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Modality
open import Applications.CombiningFeatures.Model.Modalities.Later V hiding (ω×V)
open import Applications.CombiningFeatures.Model.Modalities.Constantly V hiding (ω×V)
open import Applications.CombiningFeatures.Model.Modalities.Forever V hiding (ω×V)
open import Applications.CombiningFeatures.Model.Modalities.Bundles V hiding (ω×V)
open BaseCategory

ω×V : BaseCategory
ω×V = ω ⊗ V

private
  variable
    m n : ℕ

--------------------------------------------------
-- Interaction between the `later` and `unit` modalities

-- 𝟙 later : Modality ω×V
𝟙≤later : TwoCell 𝟙 later
transf-op (transf 𝟙≤later) = from-earlier
  {-
    transf 𝟙≤later : CtxNatTransf earlier-functor id-ctx-functor
    transf-op (transf 𝟙≤later) : (Γ : Ctx ω×V) → ctx-op earlier-functor Γ ⇒ ctx-op id-ctx-functor Γ
                                = (Γ : Ctx ω×V) → ◄ Γ ⇒ Γ
  -}
CtxNatTransf.naturality (transf 𝟙≤later) = from-earlier-natural
  {-
    σ : Δ ⇒ Γ @ ω×V

    @ ω×V : 
                                 ◄-subst σ  
    Γ,lock⟨ later ⟩ = ◄ Γ ←----------------------- ◄ Δ = Δ,lock⟨ later ⟩
                       ║                             ║
               ◄ Γ ⇒ Γ ║                             ║ ◄ Δ ⇒ Δ
                       ⇓                             ⇓
         Γ,lock⟨ 𝟙 ⟩ = Γ ←-------------------------- Δ = Δ,lock⟨ 𝟙 ⟩
                                      σ
  -}


--------------------------------------------------
-- Interaction between the `forever` and `later` modalities
-- forever : Modality ω×V V
-- later : Modality ω×V ω×V

earlier-constantly-ctx : (Γ : Ctx V) → ◄ (constantly-ctx Γ) ≅ᶜ constantly-ctx Γ
from (earlier-constantly-ctx Γ) = from-earlier (constantly-ctx Γ)
func (to (earlier-constantly-ctx Γ)) γ = γ
  {-
    RHS: 
      ? : constantly-ctx Γ ⇒ ◄ (constantly-ctx Γ) @ ω×V
    func ? {[ m , x ]} : constantly-ctx Γ ⟨ [ m , x ] ⟩ → ◄ (constantly-ctx Γ) ⟨ [ m , x ] ⟩ = Γ ⟨ x ⟩ → Γ ⟨ x ⟩
    func ? {[ m , x ]} γ = γ
  -}
_⇒_.naturality (to (earlier-constantly-ctx Γ)) = refl
  {-
                  [ m≤n , g ]
    [ m , x ] ------------------> [ n , y ]

                                    constantly-ctx Γ ⟪ [ m≤n , g ] ⟫_
    constantly-ctx Γ ⟨ [ m , x ] ⟩ <-------------------------------- constantly-ctx Γ ⟨ [ n , y ] ⟩ ∋ δ
                     ∣                                                                 ∣
    func {[ m , x ]} ∣                                                                 ∣ func {[ n , y ]}
                     ↓                                                                 ↓
    ◄ (constantly-ctx Γ) ⟨ [ m , x ] ⟩ <------------------------------------- ◄ (constantly-ctx Γ) ⟨ [ n , y ] ⟩
                                        ◄ (constantly-ctx Γ) ⟪ [ m≤n , g ] ⟫_
  
    RHS: ◄ (constantly-ctx Γ) ⟪ [ m≤n , g ] ⟫ (func {[ n , y ]} δ) ≡ func {[ m , x ]} (constantly-ctx Γ ⟪ [ m≤n , g ] ⟫ δ)
    = constantly-ctx Γ ⟪ [ m+1≤n+1 , g ] ⟫ δ ≡ constantly-ctx Γ ⟪ [ m≤n , g ] ⟫ δ
    = Γ ⟪ g ⟫ δ ≡ Γ ⟪ g ⟫ δ
  -}
eq (isoˡ (earlier-constantly-ctx Γ)) _ = ctx-id Γ
  {-
      isoˡ (earlier-constantly-ctx Γ) 
    ：to (earlier-constantly-ctx Γ) ⊚ from-earlier (constantly-ctx Γ) ≅ˢ id-subst ◄ (constantly-ctx Γ)
      eq (isoˡ (earlier-constantly-ctx Γ)) {[ m , x ]} (γ : ◄ (constantly-ctx Γ) ⟨ [ m , x ] ⟩) 
    : func (to (earlier-constantly-ctx Γ) ⊚ from-earlier (constantly-ctx Γ)) {[ m , x ]} γ 
    ≡ func (id-subst ◄ (constantly-ctx Γ)) {[ m , x ]} γ
    = func (to (earlier-constantly-ctx Γ)) ∘ func (from-earlier (constantly-ctx Γ))
        {[ m , x ]} γ
    = func (to (earlier-constantly-ctx Γ))
        (func (from-earlier (constantly-ctx Γ))
          {[ m , x ]} γ)
    = func (from-earlier (constantly-ctx Γ)) {[ m , x ]} γ
    = constantly-ctx Γ ⟪ [ m≤1+m , hom-id V ] ⟫ γ
    = Γ ⟪ hom-id V ⟫ γ
    ≡ γ
    = func (id-subst ◄ (constantly-ctx Γ)) {[ m , x ]} γ
  -}
eq (isoʳ (earlier-constantly-ctx Γ)) _ = ctx-id Γ
  {-
      isoʳ (earlier-constantly-ctx Γ)
    : from-earlier (constantly-ctx Γ) ⊚ to (earlier-constantly-ctx Γ) ≅ˢ id-subst (constantly-ctx Γ)
      eq (isoʳ (earlier-constantly-ctx Γ)) {[ m , x ]} (γ : constantly-ctx Γ ⟨ [ m , x ] ⟩)
    : func (from-earlier (constantly-ctx Γ) ⊚ to (earlier-constantly-ctx Γ)) {[ m , x ]} γ ≡ func (id-subst (constantly-ctx Γ)) γ
    = func (from-earlier (constantly-ctx Γ)) ∘ func (to (earlier-constantly-ctx Γ)) {[ m , x ]} γ ≡ γ
    = func (from-earlier (constantly-ctx Γ)) (func (to (earlier-constantly-ctx Γ)) {[ m , x ]} γ) ≡ γ
    = func (from-earlier (constantly-ctx Γ)) {[ m , x ]} γ
    = constantly-ctx Γ ⟪ m≤1+m , hom-id V {x} ⟫ γ
    = Γ ⟪ hom-id v {x} ⟫ γ
    = γ
  -}

forever-later-tyʳ : {Γ : Ctx V} (T : Ty (◄ (constantly-ctx Γ))) →
                    forever-ty (▻ T) ≅ᵗʸ forever-ty (T [ to (earlier-constantly-ctx Γ) ])
func (from (forever-later-tyʳ T)) t ⟨ m , _ ⟩' = t ⟨ suc m , _ ⟩'
  {-
    from : Γ ⊢ forever-ty (▻ T) ↣ forever-ty (T [ to (earlier-constantly-ctx Γ) ]) @ V

      func (from (forever-later-tyʳ T)) {x} {γ : Γ ⟨ x ⟩} 
    : forever-ty (▻ T) ⟨ x , γ ⟩ → forever-ty (T [ to (earlier-constantly-ctx Γ) ]) ⟨ x , γ ⟩
    = Tm ◇ (restr (▻ T) x [ const-subst γ ]) → Tm ◇ (restr (T [ to (earlier-constantly-ctx Γ) ]) x [ const-subst γ ])
      
    Γ ⊢ t : forever-ty (▻ T) ⟨ x , γ ⟩ = Tm ◇ (restr (▻ T) x [ const-subst γ ])
        t ⟨ m+1 , .tt ⟩' : restr (▻ T) x [ const-subst γ ] ⟨ m+1 , .tt ⟩ = (▻ T) ⟨ [ m+1 , x ] , γ ⟩ = T ⟨ [ m , x ] , γ ⟩
    --------------------------------------------------------------------------------------------------------------
    Γ ⊢ func (from (forever-later-tyʳ T)) t : Tm ◇ (restr (T [ to (earlier-constantly-ctx Γ) ]) x [ const-subst γ ])
        func (from (forever-later-tyʳ T)) t ⟨ m , .tt ⟩' 
      : restr (T [ to (earlier-constantly-ctx Γ) ]) x [ const-subst γ ] ⟨ m , .tt ⟩
      = restr (T [ to (earlier-constantly-ctx Γ) ]) x ⟨ m , γ ⟩
      = T [ to (earlier-constantly-ctx Γ) ] ⟨ [ m , x ] , γ ⟩
      = T ⟨ [ m , x ] , func (to (earlier-constantly-ctx Γ)) γ ⟩
      = T ⟨ [ m , x ] , γ ⟩
  -}
Tm.naturality (func (from (forever-later-tyʳ T)) t) m≤n _ = trans (ty-cong T refl) (Tm.naturality t (s≤s m≤n) refl)
_↣_.naturality (from (forever-later-tyʳ T)) = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })

func (to (forever-later-tyʳ T)) t ⟨ zero  , _ ⟩' = _
func (to (forever-later-tyʳ T)) t ⟨ suc n , _ ⟩' = t ⟨ n , tt ⟩'
Tm.naturality (func (to (forever-later-tyʳ T)) t) z≤n _ = refl
Tm.naturality (func (to (forever-later-tyʳ T)) t) (s≤s m≤n) _ = trans (ty-cong T refl) (Tm.naturality t m≤n refl)
_↣_.naturality (to (forever-later-tyʳ T)) = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → ty-cong T refl } })

eq (isoˡ (forever-later-tyʳ T)) t = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → refl } })
eq (isoʳ (forever-later-tyʳ T)) t = tm-≅-to-≡ (record { eq = λ _ → refl })

-- ω×V → V
forever-later : forever ⓜ later ≅ᵐ forever
eq-lock forever-later = earlier-constantly-ctx
  {-
      eq-lock forever-later (Γ : Ctx V) 
    : Γ ,lock⟨ forever ⓜ later ⟩ ≅ᶜ Γ ,lock⟨ forever ⟩
    = ctx-op ctx-functor (forever ⓜ later) Γ ≅ᶜ ctx-op ctx-functor forever Γ
    = ctx-op (earlier-functor ⓕ constantly-ctx-functor) Γ ≅ᶜ constantly-ctx Γ
    = ◄ (constantly-ctx Γ) ≅ᶜ constantly-ctx Γ
  -}
eq (eq-lock-natural-to forever-later σ) δ = refl
  {-
      eq-lock-natural-to forever-later {Δ Γ} (σ : Δ ⇒ Γ) 
    : to (eq-lock Γ) ⊚ lock-fmap forever σ ≅ˢ lock-fmap (forever ⓜ later) σ ⊚ to (eq-lock Δ)
    of type 
      Δ ,lock⟨ forever ⟩ ⇒ Γ ,lock⟨ forever ⓜ later ⟩
    = ctx-op (ctx-functor forever) Δ ⇒ ctx-op (ctx-functor (forever ⓜ later)) Γ
    = constantly-ctx Δ ⇒ ctx-op (ctx-functor later ⓕ ctx-functor forever) Γ
    = constantly-ctx Δ ⇒ ctx-op (ctx-functor later) (ctx-op (ctx-functor forever) Γ)
    = constantly-ctx Δ ⇒ ◄ (constantly-ctx Γ) @ ω×V
      eq (eq-lock-natural-to forever-later σ) {[ m , x ]} (γ : constantly-ctx Δ ⟨ [ m , x ] ⟩)
    : func (to (eq-lock Γ) ⊚ lock-fmap forever σ) {[ m , x ]} γ ≡ func (lock-fmap (forever ⓜ later) σ ⊚ to (eq-lock Δ)) {[ m , x ]} γ
    = func (to (eq-lock Γ)) (func (lock-fmap forever σ) {[ m , x ]} γ) ≡ func (lock-fmap (forever ⓜ later) σ) (func (to (eq-lock Δ)) {[ m , x ]} γ)
    = func (to (earlier-constantly-ctx Γ)) (func (lock-fmap forever σ) {x} γ) ≡ func (lock-fmap (forever ⓜ later) σ) (func (to (earlier-constantly-ctx Δ)) {[ m , x ]} γ)
    = func (lock-fmap forever σ) {[ m , x ]} γ ≡ func (lock-fmap (forever ⓜ later) σ) {[ m , x ]} γ
    = func (constantly-subst σ) {[ m , x ]} γ ≡ func (ctx-fmap (ctx-functor later ⓕ ctx-functor forever) σ) {[ m , x ]} γ
    = func σ {x} γ ≡ func (◄-subst (constantly-subst σ)) {[ m , x ]} γ
    = func σ {x} γ ≡ func (constantly-subst σ) {[ m+1 , x ]} γ
    = func σ {x} γ ≡ func σ {x} γ
      with 
          ctx-fmap (ctx-functor later ⓕ ctx-functor forever) σ
        = ctx-map {{is-functor (ctx-functor later ⓕ ctx-functor forever)}} σ
        = ctx-map {{composed-functor (is-functor (ctx-functor later)) (is-functor (ctx-functor forever))}} σ
        = ctx-map {{composed-functor ◄-is-functor constantly-ctx-is-functor}} σ
        = ctx-map {{◄-is-functor}} (ctx-map {{constantly-ctx-is-functor}} σ)
        = ◄-subst (constantly-subst σ)
        constantly-subst σ : constantly-ctx Δ ⇒ constantly-ctx Γ
        
        ◄-subst (constantly-subst σ) : ◄ (constantly-ctx Δ) ⇒ ◄ (constantly-ctx Γ)
  -}
eq-mod-tyʳ forever-later = forever-later-tyʳ
  {- 
    RHS: {Γ : Ctx V} (T : Ty (Γ ,lock⟨ forever ⓜ later ⟩)) → ⟨ forever ⓜ later ∣ T ⟩ ≅ᵗʸ ⟨ forever ∣ T [ to (eq-lock Γ) ] ⟩
    
      Γ ,lock⟨ forever ⓜ later ⟩ 
    = ctx-op (ctx-functor (forever ⓜ later)) Γ
    = ctx-op (ctx-functor later ⓕ ctx-functor forever) Γ
    = ctx-op (ctx-functor later) (ctx-op (ctx-functor forever) Γ)
    = ◄ (constantly-ctx Γ)

      ⟨ forever ⓜ later ∣ T ⟩
    = ⟨ forever ∣ ⟨ later | T ⟩ ⟩
    = forever-ty (▻ T)

      ⟨ forever ∣ T [ to (eq-lock Γ) ] ⟩
    = forever-ty (T [ to (eq-lock Γ) ])
  -}

forever-later'-ty : {Γ : Ctx V} (T : Ty (constantly-ctx Γ)) →
                    forever-ty (▻' T) ≅ᵗʸ forever-ty T
forever-later'-ty = eq-mod-tyˡ forever-later


--------------------------------------------------
-- Interaction between the `forever` and `constantly` modalities
-- forever : ω×V → V
-- constantly : V → ω×V

now-constantly-ctx : (Γ : Ctx V) → now (constantly-ctx Γ) ≅ᶜ Γ
func (from (now-constantly-ctx Γ)) = id
  {-
    now (constantly-ctx Γ) ⟨ x ⟩ = constantly-ctx Γ ⟨ [ 0 , x ] ⟩ = Γ ⟨ x ⟩
  -}
_⇒_.naturality (from (now-constantly-ctx Γ)) = refl
  {-
    _⇒_.naturality (from (now-constantly-ctx Γ)) {x} {y} {f : x → y}

              f
    x ------------------> y

                            now (constantly-ctx Γ) ⟪ f ⟫_
    now (constantly-ctx Γ) ⟨ x ⟩ <------------ now (constantly-ctx Γ) ⟨ y ⟩ ∋ γ
             ∣                                               ∣
    func {x} ∣                                               ∣ func {y}
             ↓                                               ↓
          Γ ⟨ x ⟩ <------------------------------------- Γ ⟨ y ⟩
                                    Γ ⟪ f ⟫_
      now (constantly-ctx Γ) ⟪ f ⟫_
    = constantly-ctx Γ ⟪ [ z≤n {0} , f ] ⟫_
    = Γ ⟪ f ⟫_
                       Γ ⟪ f ⟫_
           Γ ⟨ x ⟩ <------------ Γ ⟨ y ⟩ ∋ γ
             ∣                      ∣
    func {x} ∣                      ∣ func {y}
             ↓                      ↓
          Γ ⟨ x ⟩ <------------- Γ ⟨ y ⟩
                     Γ ⟪ f ⟫_
  -}
func (to (now-constantly-ctx Γ)) = id -- Γ ⇒ now (constantly-ctx Γ)
_⇒_.naturality (to (now-constantly-ctx Γ)) = refl
eq (isoˡ (now-constantly-ctx Γ)) _ = refl
eq (isoʳ (now-constantly-ctx Γ)) _ = refl

now-constantly-natural : {Δ : Ctx V} {Γ : Ctx V} (σ : Δ ⇒ Γ) →
                         from (now-constantly-ctx Γ) ⊚ now-subst (constantly-subst σ) ≅ˢ σ ⊚ from (now-constantly-ctx Δ)
eq (now-constantly-natural σ) _ = refl

{-
  Γ = ✲ ctx                               @ V
  constantly-ctx Γ = ✲ ← ✲ ← ✲ ← ✲ ... @ ω×V
  now (constantly-ctx Γ) = ✲ ctx         @ V
  with `now (constantly-ctx Γ) ⟨ x ⟩ = Γ ⟨ x ⟩`
  ----------------------------------------------------------
  now (constantly-ctx Γ) ⊢ T @ V
  constantly-ctx Γ ⊢ constantly-ty T @ ω×V
  Γ ⊢ forever-ty (constantly-ty T) @ V
      forever-ty (constantly-ty T) ⟨ x , γ ⟩ = Tm ◇ (restr (forever-ty (constantly-ty T)) x [ const-subst γ ])
  

  now (constantly-ctx Γ) ⊢ T @ V
  to (now-constantly-ctx Γ) : Γ ⇒ now (constantly-ctx Γ) @ V
  ----------------------------------------------------------
  Γ ⊢ T [ to (now-constantly-ctx Γ) ] @ V
      T [ to (now-constantly-ctx Γ) ] ⟨ x , γ ⟩ = T ⟨ x , γ ⟩
-}
forever-constantly-tyʳ : {Γ : Ctx V} (T : Ty (now (constantly-ctx Γ))) →
                         forever-ty (constantly-ty T) ≅ᵗʸ T [ to (now-constantly-ctx Γ) ]
func (from (forever-constantly-tyʳ {Γ} T)) {x} {γ} t = T ⟪ hom-id V {x} , trans (ctx-id Γ) (ctx-id Γ) ⟫ (t ⟨ 0 , tt ⟩')
  {- 
    from (forever-constantly-tyʳ T) : Γ ⊢ forever-ty (constantly-ty T) ↣ T [ to (now-constantly-ctx Γ) ]

    Γ @ V ⊢ 
      func (from (forever-constantly-tyʳ T)) {x} {γ : Γ ⟨ x ⟩} 
    = forever-ty (constantly-ty T) ⟨ x , γ ⟩ → T [ to (now-constantly-ctx Γ) ] ⟨ x , γ ⟩
    = Tm ◇ (restr (constantly-ty T) x [ const-subst γ ]) → T ⟨ x , γ ⟩

    Γ ⊢ func (from (forever-constantly-tyʳ T)) {x} {γ} t : T ⟨ x , γ ⟩

    ◇ ⊢ t ⟨ ?m , .tt ⟩' : (restr (constantly-ty T) x [ const-subst γ ]) ⟨ m , .tt ⟩
                         = restr (constantly-ty T) x ⟨ m , γ ⟩
                         = (constantly-ty T) ⟨ [ m , x ] , γ ⟩
                         = T ⟨ x , constantly-ctx Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ γ ⟩ 
                         = T ⟨ x , Γ ⟪ hom-id V {x} ⟫ γ ⟩
    NEED `T ⟪ hom-id V {x} , ? ⟫_ : T ⟨ x , Γ ⟪ hom-id V {x} ⟫ γ ⟩ → T ⟨ x , γ ⟩`
    γy = Γ ⟪ hom-id V {x} ⟫ γ
    γx = γ

    ? : now (constantly-ctx Γ) ⟪ hom-id V {x} ⟫ (Γ ⟪ hom-id V {x} ⟫ γ) ≡ γ
        constantly-ctx Γ ⟪ [ 0≤0 , hom-id V {x} ] ⟫ (Γ ⟪ hom-id V {x} ⟫ γ) ≡ γ
        Γ ⟪ hom-id V {x} ⟫ (Γ ⟪ hom-id V {x} ⟫ γ) ≡ γ
        
    trans (ctx-id Γ) (ctx-id Γ) : Γ ⟪ hom-id V {x} ⟫ (Γ ⟪ hom-id V {x} ⟫ γ) ≡ Γ ⟪ hom-id V {x} ⟫ γ ≡ γ
  -}
_↣_.naturality (from (forever-constantly-tyʳ T)) = trans (sym (ty-comp T)) 
                                                   (trans (ty-cong T 
                                                   (hom-idᵒ V)) (ty-comp T))
  {-
                                       T [ to (now-constantly-ctx Γ) ] ⟪ f , eγ ⟫_
    T [ to (now-constantly-ctx Γ) ] ⟨ x , γx ⟩ ←--------------------- T [ to (now-constantly-ctx Γ) ] ⟨ y , γy ⟩
                 ↑                                                                      ↑
    func (T ↣ S) |                                                                      | func (T ↣ S)
                 |                                                                      |
                 |                                                                      |
    forever-ty (constantly-ty T) ⟨ x , γx ⟩ ←--------------------- forever-ty (constantly-ty T) ⟨ y , γy ⟩ ∋ tm
                                       forever-ty (constantly-ty T) ⟪ f , eγ ⟫_

                    T ⟪ f , ty-subst-⟪_,_⟫-proof (to (now-constantly-ctx Γ)) f γy γx eγ ⟫_
            T ⟨ x , γx ⟩ ←------------------------------------------------------ T ⟨ y , γy ⟩
                 ↑                                                                      ↑
    func (T ↣ S) |                                                                      | func (T ↣ S)
                 |                                                                      |
                 |                                                                      |
    Tm ◇ (restr (constantly-ty T) x [ const-subst γx ])  ←--------------------- Tm ◇ (restr (constantly-ty T) y [ const-subst γy ]) ∋ tm
                                                  forever-ty (constantly-ty T) ⟪ f , eγ ⟫_

    Γ ⊢ T [ to (now-constantly-ctx Γ) ] ⟨ x , γx : Γ ⟨ x ⟩ ⟩ = T ⟨ x , func (to (now-constantly-ctx Γ)) γx ⟩ = T ⟨ x , γx ⟩
    Γ ⊢ forever-ty (constantly-ty T) ⟨ x , γx ⟩ = Tm ◇ (restr (constantly-ty T) x [ const-subst γx ]) 
    Γ ⊢ T [ to (now-constantly-ctx Γ) ] ⟪ f , eγ ⟫_ = T ⟪ f , ty-subst-⟪_,_⟫-proof (to (now-constantly-ctx Γ)) f γy γx eγ ⟫_
    Γ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ tm = convert-term Ty↣Tx tm
                                                    with `func Ty↣Tx {m} {tt} = constantly-ty T ⟪ [ m≤m , f ] , eγ ⟫_ = T ⟪ f , new-proof ⟫_`

      _↣_.naturality (from (forever-constantly-tyʳ T)) {x y} {g : x → y} {γy} {γx} {eγ : Γ ⟪ g ⟫ γy ≡ γx}
    : T [ to (now-constantly-ctx Γ) ] ⟪ f , eγ ⟫ (func (T ↣ S) tm) ≡ func (T ↣ S) {x} {γx} (forever-ty (constantly-ty T) ⟪ f , eγ ⟫ tm)
      

      T [ to (now-constantly-ctx Γ) ] ⟪ f , eγ ⟫ (func (T ↣ S) tm)
    ≣⟨⟩
      T ⟪ f , ty-subst-⟪_,_⟫-proof (to (now-constantly-ctx Γ)) f γy γx eγ ⟫ (func (T ↣ S) {y} {γy} tm)
    ≣⟨⟩
      T ⟪ f , _ ⟫ (T ⟪ hom-id V {y} , _ ⟫ (tm ⟨ _ , tt ⟩'))
    ≣˘⟨ ty-comp T ⟩
      T ⟪ hom-id V {y} ∙ f , _ ⟫ (tm ⟨ _ , _ ⟩')
    ≣⟨ ty-cong T (hom-idᵒ V) ⟩
      T ⟪ f ∙ hom-id V , _ ⟫ (tm ⟨ _ , _ ⟩')
    ≣⟨ ty-comp T ⟩
      T ⟪ hom-id V , _ ⟫ (T ⟪ f , _ ⟫ (tm ⟨ _ , _ ⟩'))
    ≣⟨⟩
      T ⟪ hom-id V , _ ⟫ (constantly-ty T ⟪ [ ≤-refl , f ] , eγ ⟫ (tm ⟨ _ , _ ⟩'))
    ≣⟨⟩
      T ⟪ hom-id V , _ ⟫ (func Ty↣Tx (tm ⟨ _ , _ ⟩'))
    ≣⟨⟩
      T ⟪ hom-id V , _ ⟫ ((convert-term Ty↣Tx tm) ⟨ _ , _ ⟩')
    ≣⟨⟩
      T ⟪ hom-id V {x} , _ ⟫ ((forever-ty (constantly-ty T) ⟪ f , eγ ⟫ tm) ⟨ _ , _ ⟩')
    ≣⟨⟩
      func (T ↣ S) (forever-ty (constantly-ty T) ⟪ f , eγ ⟫ tm) 

    = T ⟪ f , new-proof ⟫ 
        (T ⟪ BaseCategory.hom-id V {x} , _ ⟫ 
          (tm ⟨ m , tt ⟩')) 
    ≡ T ⟪ BaseCategory.hom-id V , _ ⟫ 
        (constantly-ty T ⟪ [ ≤-refl {m} , f ] , eγ ⟫ (tm ⟨ m , tt ⟩')
    = T ⟪ f , new-proof ⟫ (T ⟪ hom-id V {x} , _ ⟫ (tm ⟨ m , tt ⟩')) 
    ≡ T ⟪ hom-id V , _ ⟫ (T ⟪ f , new-proof ⟫ (tm ⟨ m , tt ⟩')
    = T ⟪ hom-id V ∙ f , strong ... ⟫ (tm ⟨ m , tt ⟩')
    ≡ T ⟪ f ∙ hom-id V , strong ... ⟫ (tm ⟨ m , tt ⟩')

    ty-cong (trans (BaseCategory.hom-idˡ V) (BaseCategory.hom-idʳ V))
  -}
func (to (forever-constantly-tyʳ {Γ} T)) t ⟨ m , tt ⟩' = T ⟪ hom-id V , refl ⟫ t
  {-
    to (forever-constantly-tyʳ T) : Γ ⊢ T [ to (now-constantly-ctx Γ) ] ↣ forever-ty (constantly-ty T)

      func (to (forever-constantly-tyʳ T)) {x} {γ}
    : T [ to (now-constantly-ctx Γ) ] ⟨ x , γ ⟩ → forever-ty (constantly-ty T) ⟨ x , γ ⟩ 
    = T ⟨ x , γ ⟩ → Tm ◇ (restr (constantly-ty T) x [ const-subst γ ])
    
    Γ ⊢ t : T ⟨ x , γ ⟩
    ----------------------
    Γ ⊢ func (to (forever-constantly-tyʳ T)) {x} {γ} t : Tm ◇ (restr (constantly-ty T) x [ const-subst γ ])
    what we want
    ◇ ⊢ func (to (forever-constantly-tyʳ T)) {x} {γ} t ⟨ m , tt ⟩' : restr (constantly-ty T) x [ const-subst γ ] ⟨ m , tt ⟩'
                                                                    = constantly-ty T ⟨ [ m , x ] , γ ⟩'
                                                                    = T ⟨ x , constantly-ctx Γ ⟪ [ z≤n , hom-id V ] ⟫ γ ⟩
                                                                    = T ⟨ x , Γ ⟪ hom-id V ⟫ γ ⟩
    T ⟪ hom-id V {x} , refl ⟫_ : T ⟨ x , γ ⟩ → T ⟨ x , Γ ⟪ hom-id V ⟫ γ ⟩
  -}
Tm.naturality (func (to (forever-constantly-tyʳ T)) t) _ _ = strong-ty-id T
_↣_.naturality (to (forever-constantly-tyʳ T)) = tm-≅-to-≡ (record { eq = λ _ → trans (sym (ty-comp T)) (trans (ty-cong T (hom-idᵒ V)) (ty-comp T)) })
  {- 
                                                    forever-ty (constantly-ty T) ⟪ f , eγ ⟫_
    Tm ◇ (restr (constantly-ty T) x [ const-subst γx ])  ←--------------------- Tm ◇ (restr (constantly-ty T) y [ const-subst γy ]) 
                   ↑                                                                             ↑
    func (_↣_) {x} |                                                                             | func (_↣_) {y}
                   |                                                                             |
                   |                                                                             |
                T ⟨ x , γx ⟩ ←----------------------------------------------------------- T ⟨ y , γy ⟩ ∋ t
                                                  T ⟪ f , ■ ⟫_
    
    Γ ⊢ T [ to (now-constantly-ctx Γ) ] ⟨ x , γx ⟩ = T ⟨ x , func (to (now-constantly-ctx Γ)) γx ⟩ = T ⟨ x , γx ⟩
    Γ ⊢ forever-ty (constantly-ty T) ⟨ x , γx ⟩ = Tm ◇ (restr (constantly-ty T) x [ const-subst γx ]) 

    Γ ⊢ T [ to (now-constantly-ctx Γ) ] ⟪ f , eγ ⟫_ = T ⟪ f , ■ = ty-subst-⟪_,_⟫-proof (to (now-constantly-ctx Γ)) f γy γx eγ ⟫_
    Γ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ t = convert-term Ty↣Tx t : Tm ◇ (restr (constantly-ty T) x [ const-subst γx ])
    ◇ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ t ⟨ m , tt ⟩' = func Ty↣Tx {m} {tt} (t ⟨ m , tt ⟩')
                                                               = constantly-ty T ⟪ [ m≤m , f ] , eγ ⟫ (t ⟨ m , tt ⟩')
                                                               = T ⟪ f , ▣ ⟫ (t ⟨ m , tt ⟩')
    ◇ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ t ⟨ m , tt ⟩' : restr (constantly-ty T) x [ const-subst γx ] ⟨ m , tt ⟩
                                                               = constantly-ty T ⟨ [ m , x ] , γx ⟩
                                                               = T ⟨ x , constantly-ctx Γ ⟪ z≤n , hom-id V {x} ⟫ γx ⟩
                                                               = T ⟨ x , Γ ⟪ hom-id V {x} ⟫ γx ⟩
    
    RHS:
      Γ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ (func (_↣_) {y} t) ≡ func (_↣_) {x} (T ⟪ f , ■ ⟫ t) : Tm ◇ (restr (constantly-ty T) x [ const-subst γx ])

    ◇ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ (func (_↣_) {y} t) : restr (constantly-ty T) x [ const-subst γx ]
    ◇ ⊢ func (_↣_) {x} (T ⟪ f , ■ ⟫ t) : restr (constantly-ty T) x [ const-subst γx ]
    ◇ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ (func (_↣_) {y} t) ≅ᵗᵐ func (_↣_) {x} (T ⟪ f , ■ ⟫ t) 


    ◇ ⊢ forever-ty (constantly-ty T) ⟪ f , eγ ⟫ (func (_↣_) {y} t) ⟨ m , tt ⟩' : T ⟨ x , Γ ⟪ hom-id V {x} ⟫ γx ⟩
    ◇ ⊢ func (_↣_) {x} (T ⟪ f , ■ ⟫ t) ⟨ m , tt ⟩' : T ⟨ x , Γ ⟪ hom-id V {x} ⟫ γx ⟩
    -------------------------------------------------------------------------------------------------------------------------------------
    ◇ ⊢ eq {m} tt : forever-ty (constantly-ty T) ⟪ f , eγ ⟫ (func (_↣_) {y} t) ⟨ m , tt ⟩' ≡ func (_↣_) {x} (T ⟪ f , ■ ⟫ t) ⟨ m , tt ⟩'

      forever-ty (constantly-ty T) ⟪ f , eγ ⟫ (func (_↣_) {y} t) ⟨ m , tt ⟩'
    ≡⟨⟩
      T ⟪ f , ▣ ⟫ (func (_↣_) {y} t ⟨ m , tt ⟩')
    ≡⟨⟩
      T ⟪ f , ▣ ⟫ (T ⟪ hom-id V {y} , refl ⟫ t)
    ≡⟨ sym (ty-comp T) ⟩
      T ⟪ hom-id V {y} ∙ f ,  strong-ctx-id-comp ... ⟫ t
    ≡⟨ ty-cong T (hom-idᵒ V) ⟩
      T ⟪ f ∙ hom-id V {x} , strong-ctx-comp-id ... ⟫ t
    ≡⟨ ty-comp T ⟩
      T ⟪ hom-id V {x} , refl ⟫ (T ⟪ f , ■ ⟫ t)
    ≡⟨⟩
      func (_↣_) {x} (T ⟪ f , ■ ⟫ t) ⟨ m , tt ⟩'
  -}
eq (isoˡ (forever-constantly-tyʳ {Γ} T)) {x = x} {γ} t = tm-≅-to-≡ (record { eq = eqn })
  where
    eqn : ∀ {m} δ → func (to (forever-constantly-tyʳ T)) {x} {γ} (func (from (forever-constantly-tyʳ T)) {x} {γ} t) ⟨ m , δ ⟩' ≡ t ⟨ m , δ ⟩'
    eqn {m} tt = 
      begin
        func (to (forever-constantly-tyʳ {Γ} T)) {x} {γ} (func (from (forever-constantly-tyʳ T)) {x} {γ} t) ⟨ m , tt ⟩'
      ≡⟨⟩
        func (to (forever-constantly-tyʳ T)) {x} {γ} (T ⟪ hom-id V {x} , trans (ctx-id Γ) (ctx-id Γ) ⟫ (t ⟨ 0 , tt ⟩')) ⟨ m , tt ⟩'
      ≡⟨⟩
        T ⟪ hom-id V , refl ⟫ (T ⟪ hom-id V {x} , trans (ctx-id Γ) (ctx-id Γ) ⟫ (t ⟨ 0 , tt ⟩'))
      ≡˘⟨ ty-comp T ⟩
        T ⟪ (_∙_) V (hom-id V {x}) (hom-id V {x}) , _ ⟫ (t ⟨ 0 , tt ⟩')
      ≡⟨ ty-cong T (hom-idˡ V) ⟩
        T ⟪ hom-id V {x} , ctx-id Γ ⟫ (t ⟨ 0 , tt ⟩')
      ≡⟨ strong-ty-id T ⟩
        t ⟨ 0 , tt ⟩'
      ≡˘⟨ Tm.naturality t {0} {m} z≤n refl ⟩
        T ⟪ hom-id V {x} , _ ⟫ t ⟨ m , tt ⟩'
      ≡⟨ strong-ty-id T ⟩
        t ⟨ m , tt ⟩' ∎
      where open ≡-Reasoning
  {- 
    Γ ⊢ isoˡ (forever-constantly-tyʳ T) : (to (forever-constantly-tyʳ T)) ⊙ (from (forever-constantly-tyʳ T)) ≅ⁿ id-trans (forever-ty (constantly-ty T))
      eq (isoˡ (forever-constantly-tyʳ T)) {x} {γ} t 
    : func ((to (forever-constantly-tyʳ T)) ⊙ (from (forever-constantly-tyʳ T))) {x} {γ} t ≡ func (id-trans (forever-ty (constantly-ty T))) {x} {γ} t
    = func (to (forever-constantly-tyʳ T)) {x} {γ} (func (from (forever-constantly-tyʳ T)) {x} {γ} t) ≡ t
    = func (to (forever-constantly-tyʳ T)) {x} {γ} (T ⟪ hom-id V {x} , trans (ctx-id Γ) (ctx-id Γ) ⟫ (t ⟨ _ , tt ⟩')) ≡ t
    
    GOAL : 
      eq {m} tt : func (to (forever-constantly-tyʳ T)) {x} {γ} (T ⟪ hom-id V {x} , trans (ctx-id Γ) (ctx-id Γ) ⟫ (t ⟨ _ , tt ⟩')) ⟨ m , tt ⟩' ≡ t ⟨ m , tt ⟩'

    t : Tm ◇ (restr (constantly-ty T) x [ const-subst γ ])
    ◇ ⊢ t ⟨ m , tt ⟩' : restr (constantly-ty T) x [ const-subst γ ] ⟨ m , tt ⟩ 
                       = T ⟨ x , Γ ⟪ hom-id V ⟫ γ ⟩
      Tm.naturality {x = 0} {y = n} {γy = tt} {γx = tt} z≤n (e-tt : ◇ ⟪ z≤n ⟫ tt ≡ tt)
    : restr (constantly-ty T) x [ const-subst γ ] ⟪ z≤n , e-tt ⟫ t ⟨ n , tt ⟩' ≡ t ⟨ 0 , tt ⟩'
    = constantly-ty T ⟪ [ z≤n , hom-id V {x} ] , e-tt ⟫ t ⟨ n , tt ⟩' ≡ t ⟨ 0 , tt ⟩'
    = T ⟪ hom-id V {x} , new-proof ⟫ t ⟨ n , tt ⟩' ≡ t ⟨ 0 , tt ⟩'
  -}
eq (isoʳ (forever-constantly-tyʳ T)) _ = trans (sym (ty-comp T)) (trans (ty-cong T (hom-idˡ V)) (ty-id T))
  {-  
    Γ ⊢ isoʳ (forever-constantly-tyʳ T) : (from (forever-constantly-tyʳ {Γ} T)) ⊙ (to (forever-constantly-tyʳ T) ≅ⁿ id-trans (T [ to (now-constantly-ctx Γ) ]) : T [ to (now-constantly-ctx Γ) ] ↣ T [ to (now-constantly-ctx Γ) ]
      eq (isoʳ (forever-constantly-tyʳ T)) {x} {γ} (t : T [ to (now-constantly-ctx Γ) ] ⟨ x , γ ⟩)
    : func ((from (forever-constantly-tyʳ {Γ} T)) ⊙ (to (forever-constantly-tyʳ T)) t ≡ func (id-trans (T [ to (now-constantly-ctx Γ) ])) t
    = func (from (forever-constantly-tyʳ {Γ} T)) (func (to (forever-constantly-tyʳ T)) {x} {γ} t) ≡ t : T ⟨ x , γ ⟩

      func (from (forever-constantly-tyʳ {Γ} T)) (func (to (forever-constantly-tyʳ T)) {x} {γ} t)
    ≡⟨⟩
      T ⟪ hom-id V {x} , trans (ctx-id Γ) (ctx-id Γ) ⟫ (func (to (forever-constantly-tyʳ T)) {x} {γ} t ⟨ _ , tt ⟩')
    ≡⟨⟩
      T ⟪ hom-id V , trans (ctx-id Γ) (ctx-id Γ) ⟫ (T ⟪ hom-id V , refl ⟫ t)
    ≡˘⟨ ty-comp T ⟩
      T ⟪ (_∙_) V (hom-id V {x}) (hom-id V {x}) , _ ⟫ t
    ≡⟨ ty-cong T (hom-idˡ V) ⟩
      T ⟪ hom-id V , ctx-id Γ ⟫ t
    ≡⟨ ty-id T ⟩
      t
  -}

-- V → V
forever-constantly : forever ⓜ constantly ≅ᵐ 𝟙
eq-lock forever-constantly = now-constantly-ctx
  {-
    eq-lock forever-constantly (Γ : Ctx V) : Γ ,lock⟨ forever ⓜ constantly ⟩ ≅ᶜ Γ ,lock⟨ 𝟙 ⟩
    = ctx-op (ctx-functor forever ⓜ constantly) Γ ≅ᶜ ctx-op (ctx-functor 𝟙) Γ
    = ctx-op (ctx-functor constantly ⓕ ctx-functor forever) Γ ≅ᶜ ctx-op id-ctx-functor Γ
    = ctx-op (ctx-functor constantly) (ctx-op (ctx-functor forever) Γ) ≅ᶜ Γ
    = now (constantly-ctx Γ) ≅ᶜ Γ
  -}
eq (eq-lock-natural-to forever-constantly σ) δ = refl
eq-mod-tyʳ forever-constantly = forever-constantly-tyʳ
  {-
    eq-mod-tyʳ forever-constantly {Γ : Ctx V} T

    Γ ,lock⟨ 𝟙 ⟩ ⊢ T [ to (eq-lock Γ) ] @ V
        ║
        ║ to (eq-lock Γ)
        ⇓
    Γ ,lock⟨ forever ⓜ constantly ⟩ ⊢ T @ V
    --------------------------------------------------------------------------------
    Γ ⊢ ⟨ forever ⓜ constantly ∣ T ⟩ ≅ᵗʸ ⟨ 𝟙 ∣ T [ to (now-constantly-ctx Γ) ] ⟩
        = ⟨ forever | ⟨ constantly | T ⟩ ⟩ ≅ᵗʸ T [ to (now-constantly-ctx Γ) ]
        = forever-ty (constantly-ty T) ≅ᵗʸ T [ to (now-constantly-ctx Γ) ]
  -}


--------------------------------------------------
-- Interaction between the `unit` and `constantly ⓜ forever` modalities

{-
    Γ ,lock⟨ forever ⓜ constantly ⟩ = lock (forever ⓜ constantly) Γ
  = ctx-op (ctx-functor (forever ⓜ constantly)) Γ
  = ctx-op (ctx-functor constantly ⓕ ctx-functor forever) Γ
  = ctx-op (ctx-functor constantly) (ctx-op (ctx-functor forever) Γ)
  = lock constantly (lock forever Γ)
  = lock constantly (Γ ,lock⟨ forever ⟩)
  = (Γ ,lock⟨ forever ⟩) ,lock⟨ constantly ⟩

    eq-mod-closed forever-constantly A {Γ : Ctx V}
  : ⟨ forever ⓜ constantly ∣ A {Γ ,lock⟨ forever ⓜ constantly ⟩} ⟩ ≅ᵗʸ ⟨ 𝟙 ∣ A ⟩
  = ⟨ forever ⓜ constantly ∣ A {(Γ ,lock⟨ forever ⟩) ,lock⟨ constantly ⟩} ⟩ ≅ᵗʸ A
  = ⟨ forever | ⟨ constantly | A {(Γ ,lock⟨ forever ⟩) ,lock⟨ constantly ⟩} ⟩ ⟩ ≅ᵗʸ A
  = forever-ty (constantly-ty A {(Γ ,lock⟨ forever ⟩) ,lock⟨ constantly ⟩} ) ≅ᵗʸ A
  = forever-ty (constantly-ty A) ≅ᵗʸ A

  Γ ⊢ t : A @ V
  ----------------------------------------------------------------------------------
  Γ ⊢ ι[ eq-mod-closed forever-constantly A ] t : forever-ty (constantly-ty A) @ V
  -----------------------------------------------------------------------------------------------------
  constantly-ctx Γ ⊢ unforever-tm (ι[ eq-mod-closed forever-constantly A ] t) : constantly-ty A @ ω×V
  ------------------------------------------------------------------------------------------------------------
  now (constantly-ctx Γ) ⊢ unconstantly-tm (unforever-tm (ι[ eq-mod-closed forever-constantly A ] t)) : A @ V
-}
now-constantly-ctx-intro : {A : ClosedTy V} {{_ : IsClosedNatural A}} {Γ : Ctx V} →
                           Tm Γ A → Tm (now (constantly-ctx Γ)) A
now-constantly-ctx-intro {A} t = unconstantly-tm (unforever-tm (ι[ eq-mod-closed forever-constantly A ] t))

to-constantly-now-ctx : (Γ : Ctx ω×V) → (Γ ⇒ constantly-ctx (now Γ))
func (to-constantly-now-ctx Γ) = Γ ⟪ [ z≤n , hom-id V ] ⟫_
  {- 
      func (to-constantly-now-ctx Γ) {[ m , x ]}
    : Γ ⟨ [ m , x ] ⟩ → constantly-ctx (now Γ) ⟨ [ m , x ] ⟩
    = Γ ⟨ [ m , x ] ⟩ → now Γ ⟨ x ⟩
    = Γ ⟨ [ m , x ] ⟩ → Γ ⟨ [ 0 , x ] ⟩
    = Γ ⟪ [ z≤n {m} , hom-id V ] ⟫ 
  -}
_⇒_.naturality (to-constantly-now-ctx Γ) {x = [ m , x ]} {y = [ n , y ]} {[ m≤n , g ]} {δ = γ} =
  begin
    constantly-ctx (now Γ) ⟪ [ m≤n , g ] ⟫ (func (to-constantly-now-ctx Γ) {[ n , y ]} γ)
  ≡⟨⟩
    now Γ ⟪ g ⟫ (func (to-constantly-now-ctx Γ) {[ n , y ]} γ)
  ≡⟨⟩
    Γ ⟪ [ z≤n {0} , g ] ⟫ (Γ ⟪ [ z≤n {n} , hom-id V ] ⟫ γ) 
  ≡⟨ sym (ctx-comp Γ) ⟩
    Γ ⟪ [ (_∙_) ω (z≤n {n}) (z≤n {0}) , (_∙_) V (hom-id V) g ] ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩
    Γ ⟪ [ z≤n {n} , g ] ⟫ γ
  ≡˘⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idʳ V ]) ⟩
    Γ ⟪ [ (_∙_) ω m≤n (z≤n {m}) , (_∙_) V g (hom-id V) ] ⟫ γ
  ≡⟨ ctx-comp Γ ⟩
    Γ ⟪ [ z≤n {m} , hom-id V {x} ] ⟫ (Γ ⟪ [ m≤n , g ] ⟫ γ)
  ≡⟨⟩
    func (to-constantly-now-ctx Γ) {[ m , x ]} (Γ ⟪ [ m≤n , g ] ⟫ γ) ∎
  where open ≡-Reasoning

to-constantly-now-ctx-natural : {Δ Γ : Ctx ω×V} (σ : Δ ⇒ Γ) →
    to-constantly-now-ctx Γ ⊚ σ ≅ˢ ctx-fmap (constantly-ctx-functor ⓕ now-functor) σ ⊚ to-constantly-now-ctx Δ
eq (to-constantly-now-ctx-natural σ) δ = _⇒_.naturality σ
  {-
      eq (to-constantly-now-ctx-natural σ) {[ m , x ]} (δ : Δ ⟨ [ m , x ] ⟩)
    : func (to-constantly-now-ctx Γ ⊚ σ) {[ m , x ]} δ ≡ func (ctx-fmap (constantly-ctx-functor ⓕ now-functor) σ ⊚ to-constantly-now-ctx Δ) {[ m , x ]} δ
    
      func (to-constantly-now-ctx Γ ⊚ σ) {[ m , x ]} δ
    ≡⟨⟩
      func (to-constantly-now-ctx Γ) (func σ {[ m , x ]} δ)
    ≡⟨⟩
      Γ ⟪ [ z≤n , hom-id V ] ⟫ (func σ {[ m , x ]} δ)
    ≡⟨⟩
      func σ {x} (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (now-subst σ) {x} (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (constantly-subst (now-subst σ)) {[ _ , x ]} (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (ctx-map (constantly-ctx-is-functor) (ctx-map (now-is-functor) σ)) (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (ctx-map (is-functor constantly-ctx-functor) (ctx-map (is-functor now-functor) σ)) (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (ctx-map (composed-functor (is-functor constantly-ctx-functor) (is-functor now-functor)) σ) (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (ctx-map {{is-functor (constantly-ctx-functor ⓕ now-functor)}} σ) (Γ ⟪ [ z≤n , hom-id V ] ⟫ δ)
    ≡⟨⟩
      func (ctx-fmap (constantly-ctx-functor ⓕ now-functor) σ) (func (to-constantly-now-ctx Δ) {[ m , x ]} δ)
    ≡⟨⟩
      func (ctx-fmap (constantly-ctx-functor ⓕ now-functor) σ ⊚ to-constantly-now-ctx Δ) {[ m , x ]} δ
  -}

-- ω×V → ω×V
constantly∘forever≤𝟙 : TwoCell (constantly ⓜ forever) 𝟙
transf-op (transf constantly∘forever≤𝟙) = to-constantly-now-ctx
  {-
    transf constantly∘forever≤𝟙 : CtxNatTransf (ctx-functor 𝟙) (ctx-functor (constantly ⓜ forever))
                                = CtxNatTransf id-ctx-functor (ctx-functor forever ⓕ ctx-functor constantly)
    transf-op (self) : (Γ : Ctx ω×V) → ctx-op id-ctx-functor Γ ⇒ ctx-op (ctx-functor forever ⓕ ctx-functor constantly) Γ
                    = (Γ : Ctx ω×V) → Γ ⇒ constantly-ctx (now Γ)
  -}
CtxNatTransf.naturality (transf constantly∘forever≤𝟙) = to-constantly-now-ctx-natural

{-
  constantly-ctx (now Γ) ⊢ T @ ω×V
  now Γ ⊢ forever-ty T @ V
  Γ ⊢ constantly-ty (forever-ty T) @ ω×V
  Γ ⊢ T [ to-constantly-now-ctx Γ ] @ ω×V

  Γ ⊢ t : constantly-ty (forever-ty T) @ ω×V
  ------------------------------------------------------------------
  Γ ⊢ from-constantly-forever-ty t : T [ to-constantly-now-ctx Γ ]
-}
from-constantly-forever-ty : {Γ : Ctx ω×V} {T : Ty (constantly-ctx (now Γ))} →
                             Tm Γ (constantly-ty (forever-ty T)) → Tm Γ (T [ to-constantly-now-ctx Γ ])
from-constantly-forever-ty {Γ = Γ} t = unforever-tm (unconstantly-tm t) [ to-constantly-now-ctx Γ ]'
  {-
    Γ ⊢ t : constantly-ty (forever-ty T)
         t ⟨ [ m , x ] , γ ⟩' : constantly-ty (forever-ty T) ⟨ [ m , x ] , γ ⟩ 
                              = forever-ty T ⟨ x , Γ ⟪ [ 0≤m , hom-id V {x} ] ⟫ γ ⟩
                              = Tm ◆ (restr T x [ const-subst Γ ⟪ [ 0≤m , hom-id V {x} ] ⟫ γ ])
    now Γ ⊢ unconstantly-tm t : forever-ty T @ V
    constantly-ctx (now Γ) ⊢ unforever-tm (unconstantly-tm t) : T @ ω×V
    to-constantly-now-ctx Γ : Γ ⇒ constantly-ctx (now Γ) @ ω×V
    --------------------------------------------------------------------------------------------------------
    Γ ⊢ unforever-tm (unconstantly-tm t) [ to-constantly-now-ctx Γ ]' : T [ to-constantly-now-ctx Γ ] @ ω×V
  -}
