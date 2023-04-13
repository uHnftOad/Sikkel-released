--------------------------------------------------
-- The constantly-forever dependent adjunction
--------------------------------------------------
open import Model.BaseCategory

module Applications.CombiningFeatures.Model.Modalities.Forever (V : BaseCategory) where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure

open BaseCategory

ω×V : BaseCategory
ω×V = ω ⊗ V

private
  variable
    x : Ob V
    Δ Γ Θ : Ctx V


--------------------------------------------------
-- The context operation

{-
  Γ = ✲ ctx                               @ V
  --------------------------------------------
  constantly-ctx Γ = ✲ ← ✲ ← ✲ ← ✲ ... @ ω×V

  The context operator `_,lock⟨ forever ⟩` of modality `forever` 
-}
constantly-ctx : Ctx V → Ctx ω×V
constantly-ctx Γ ⟨ [ _ , x ] ⟩ = Γ ⟨ x ⟩
constantly-ctx Γ ⟪ [ _ , g ] ⟫ γ = Γ ⟪ g ⟫ γ
ctx-id (constantly-ctx Γ) = ctx-id Γ
ctx-comp (constantly-ctx Γ) = ctx-comp Γ

{- 
  The action of `constantly-ctx` on the morphisms (i.e., context substitutions) of Psh(V)

      Δ⟨✲⟩
  σ :   ↓
      Γ⟨✲⟩                                                 @ V
  -------------------------------------------------------------
                        Δ⟨✲⟩ ← Δ⟨✲⟩ ← Δ⟨✲⟩ ← Δ⟨✲⟩ ...  @ ω×V
  constantly-subst σ :   ↓σ      ↓σ     ↓σ      ↓σ
                        Γ⟨✲⟩ ← Γ⟨✲⟩ ← Γ⟨✲⟩ ← Γ⟨✲⟩ ...

-}
constantly-subst : Δ ⇒ Γ → constantly-ctx Δ ⇒ constantly-ctx Γ
func (constantly-subst σ) {[ _ , x ]} = func σ {x}
_⇒_.naturality (constantly-subst σ) = _⇒_.naturality σ

-- The action of `constantly-ctx` on the morphisms of Psh(V) respects equivalence `_≅ˢ_` of morphisms/substitutions.
constantly-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → constantly-subst σ ≅ˢ constantly-subst τ
eq (constantly-subst-cong σ=τ) δ = eq σ=τ δ

-- The action of `constantly-ctx` on the morphisms of Psh(V) preserves the identity morphisms/substitutions.
constantly-subst-id : constantly-subst (id-subst Γ) ≅ˢ id-subst (constantly-ctx Γ)
eq constantly-subst-id _ = refl

-- The action of `constantly-ctx` on the morphisms of Psh(V) commutes with substitution composition (i.e., the composition operation of Psh(V)).
constantly-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → constantly-subst (σ ⊚ τ) ≅ˢ constantly-subst σ ⊚ constantly-subst τ
eq (constantly-subst-⊚ σ τ) _ = refl

-- A proof that `constantly-ctx` is a functor
instance
  constantly-ctx-is-functor : IsCtxFunctor constantly-ctx
  ctx-map {{constantly-ctx-is-functor}} = constantly-subst
  ctx-map-cong {{constantly-ctx-is-functor}} = constantly-subst-cong
  ctx-map-id {{constantly-ctx-is-functor}} = constantly-subst-id
  ctx-map-⊚ {{constantly-ctx-is-functor}} = constantly-subst-⊚


--------------------------------------------------
-- The `forever` modality and corresponding term formers

-- A context constructor from ω×V to ω
_<at>_ : Ctx ω×V → Ob V → Ctx ω
(Ω <at> x) ⟨ m ⟩ = Ω ⟨ [ m , x ] ⟩
(Ω <at> x) ⟪ m≤n ⟫ γ = Ω ⟪ [ m≤n , hom-id V {x} ] ⟫ γ
ctx-id (Ω <at> x) = ctx-id Ω
ctx-comp (Ω <at> x) {γ = γ} = trans (cong (Ω ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ V) ])) (ctx-comp Ω)
  {- Detailed proof
    ctx-comp (Ω <at> x) {f = k≤m} {g = m≤n} {γ = γ} = 
      begin
        (Ω <at> x) ⟪ (_∙_) ω m≤n k≤m ⟫ γ
      ≡⟨⟩
        Ω ⟪ [ (_∙_) ω m≤n k≤m , hom-id V ] ⟫ γ
      ≡⟨ cong (Ω ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ V) ]) ⟩
        Ω ⟪ [ (_∙_) ω m≤n k≤m , (_∙_) V (hom-id V) (hom-id V) ] ⟫ γ
      ≡⟨ ctx-comp Ω ⟩
        Ω ⟪ [ k≤m , hom-id V ] ⟫ (Ω ⟪ [ m≤n , hom-id V ] ⟫ γ)
      ≡⟨⟩
        (Ω <at> x) ⟪ k≤m ⟫ ((Ω <at> x) ⟪ m≤n ⟫ γ) ∎
      where open ≡-Reasoning
  -}

{-
  A morphism/substitution constructor of Psh(ω)

                                        ◇ ⟪ m≤n ⟫_
                  ◇ ⟨ m ⟩ <-------------------------------------- ◇ ⟨ n ⟩ ∋ tt
                      ∣                                                ∣
             func {m} ∣                                                ∣ func {n}
                      ↓                                                ↓
  ((constantly-ctx Γ) <at> x) ⟨ m ⟩ <------------ ((constantly-ctx Γ) <at> x) ⟨ n ⟩
                            ((constantly-ctx Γ) <at> x) ⟪ m≤n ⟫_

  Morphism `◇ ⇒ (constantly-ctx Γ <at> x)` is a map `⊤ → Γ ⟨ x ⟩` at each n. It essentially assigns to each n an Agda term of type `Γ ⟨ x ⟩`.
-}
const-subst : Γ ⟨ x ⟩ → ◇ ⇒ ((constantly-ctx Γ) <at> x)
func (const-subst γ) _ = γ
_⇒_.naturality (const-subst {Γ = Γ} γ) = ctx-id Γ

-- The substitution constructor `const-subst` respects equality of Agda terms.
const-subst-cong : {γ γ' : Γ ⟨ x ⟩} → γ ≡ γ' → const-subst {Γ = Γ} γ ≅ˢ const-subst γ'
eq (const-subst-cong eγ) tt = eγ

restr : Ty (constantly-ctx Γ) → (x : Ob V) → Ty ((constantly-ctx Γ) <at> x)
restr T x ⟨ m , γ ⟩ = T ⟨ [ m , x ] , γ ⟩
-- γ : ((constantly-ctx Γ) <at> x) ⟨ m ⟩ 
--   = (constantly-ctx Γ) ⟨ [ m , x ] ⟩
restr T x ⟪ m≤n , eγ ⟫ t = T ⟪ [ m≤n , hom-id V ] , eγ ⟫ t
ty-cong (restr T x) e-hom = ty-cong T (×-≡,≡→≡ [ e-hom , refl ])
ty-id (restr T x) = ty-id T
ty-comp (restr {Γ = Γ} T x) = trans (ty-cong T (×-≡,≡→≡ [ refl , sym (hom-idˡ V) ])) (ty-comp T)
  {- Detailed proof
    ty-comp (restr {Γ = Γ} T x) {f = k≤m} {g = m≤n} {γz = γn} {γy = γm} {γx = γk} {eγ-nm} {eγ-mk} = 
      begin
        restr T x ⟪ (_∙_) ω m≤n k≤m , strong-ctx-comp ((constantly-ctx Γ) <at> x) eγ-nm eγ-mk ⟫ _
      ≡⟨⟩
        T ⟪ [ (_∙_) ω m≤n k≤m , hom-id V ] , strong-ctx-comp ((constantly-ctx Γ) <at> x) eγ-nm eγ-mk ⟫ _
      ≡⟨ ty-cong T (×-≡,≡→≡ [ refl , sym (hom-idˡ V) ]) ⟩
        T ⟪ [ (_∙_) ω m≤n k≤m , (_∙_) V (hom-id V) (hom-id V) ] , strong-ctx-comp Γ eγ-nm eγ-mk ⟫ _
      ≡⟨ ty-comp T ⟩
        T ⟪ [ k≤m , hom-id V ] , eγ-mk ⟫ (T ⟪ [ m≤n , hom-id V ] , eγ-nm ⟫ _)
      ≡⟨⟩
        restr T x ⟪ k≤m , eγ-mk ⟫ ((restr T x) ⟪ m≤n , eγ-nm ⟫ _) ∎
      where open ≡-Reasoning
  -}
restr-cong : {T : Ty (constantly-ctx Γ)} {S : Ty (constantly-ctx Γ)} {x : Ob V} → T ≅ᵗʸ S → restr T x ≅ᵗʸ restr S x 
func (from (restr-cong {x = x} T=S)) {m} {γ} = func (from T=S) {[ m , x ]} {γ}
_↣_.naturality (from (restr-cong T=S)) = _↣_.naturality (from T=S)
func (to (restr-cong {x = x} T=S)) {m} {γ} = func (to T=S) {[ m , x ]} {γ}
_↣_.naturality (to (restr-cong T=S)) = _↣_.naturality (to T=S)
eq (isoˡ (restr-cong T=S)) = eq (isoˡ T=S)
eq (isoʳ (restr-cong T=S)) = eq (isoʳ T=S)

{-   
  Γ = ✲ ctx @ V
  constantly-ctx Γ = ✲ ← ✲ ← ✲ ← ✲ ... @ ω×V
  -------------------------------------------------
  constantly-ctx Γ <at> x = • ← • ← • ← ... @ ω

  constantly-ctx Γ ⊢ T = ✲ ← ✲ ← ✲ ← ✲ ... @ ω×V
  -----------------------------------------------------------------
  constantly-ctx Γ <at> x ⊢ restr T = • ← • ← • ← ... @ ω
  const-subst γ : ◇ ⇒ (constantly-ctx Γ <at> x)
  ------------------------------------------------------------------------------------
  ◇ ⊢ (restr T x) [ const-subst γ ] = • ← • ← • ← ... @ ω
       with (restr T x) [ const-subst γ ] ⟨ m , tt ⟩ 
          = restr T x ⟨ m , γ ⟩ 
          = T ⟨ [ m , x ] , γ ⟩
  ◇ ⊢ t : (restr T x) [ const-subst γ ] = • ← • ← • ← ... @ ω
       with t ⟨ m , tt ⟩' : T ⟨ [ m , x ] , γ ⟩
  --------------------------
  Γ ⊢ forever-ty T : ✲ @ V
              
              g
  x -----------------→ y

                                      forever-ty T ⟪ g , eγ ⟫_ 
  Tm ◇ (restr T y [ const-subst γy ]) -------------→ Tm ◇ (restr T x [ const-subst γx ])
               t ⟨ m , tt ⟩' |-----------------------------→ T ⟪ [ m≤m, g ] , eγ ⟫ (t ⟨ m , tt ⟩')

  `forever-ty T` is NOT time dependent. The time-related information of T is encoded in the fact that `forever-ty T ⟨ x , γ ⟩` is contains terms that can be indexed by time.
-}
forever-ty : Ty (constantly-ctx Γ) → Ty Γ
forever-ty T ⟨ x , γ ⟩ = Tm ◇ (restr T x [ const-subst γ ])
_⟪_,_⟫_ (forever-ty {Γ = Γ} T) {x} {y} g {γy} {γx} eγ t = convert-term Ty↣Tx t
  {-
    {x y : Ob v} 
    g : x → y 
    {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} 
    eγ : Γ ⟪ g ⟫ γy ≡ γx 
    t : forever-ty T ⟨ y , γy ⟩
  -}
  where
    Ty↣Tx : restr T y [ const-subst γy ] ↣ restr T x [ const-subst γx ]
    func Ty↣Tx {m} {tt} = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫_
      {-
        RHS : 
          restr T y [ const-subst γy ] ⟨ m , tt ⟩ → restr T x [ const-subst γx ] ⟨ m , tt ⟩
        = restr T y ⟨ m , γy ⟩ →  restr T x ⟨ m , γx ⟩
        = T ⟨ [ m , y ] , γy ⟩ → T ⟨ [ m , x ] , γx ⟩
        γy : Γ ⟨ y ⟩ = constantly-ctx Γ ⟨ [ _ , y ] ⟩
        γx : Γ ⟨ x ⟩ = constantly-ctx Γ ⟨ [ _ , x ] ⟩
        eγ : Γ ⟪ g ⟫ γy ≡ γx 
      -}
    _↣_.naturality Ty↣Tx {m} {n} {m≤n} {tt} {tt} {e-tt} {t} = trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idⁱ V ])) (ty-comp T))
      {-
        {m n : ob ω} {m≤n} {tt : ◇ ⟨ _ ⟩} {e-tt : ◇ ⟨ m≤n ⟩ tt ≡ tt} {t : T ⟨ [ n , y ] , γy ⟩}
                                      Tx ⟪ m≤n , e-tt ⟫_
                      Tx ⟨ m , tt ⟩ ←--------------------- Tx ⟨ n , tt ⟩
                            ↑                                    ↑
        func Ty↣Tx {m} {tt} |                                    | func Ty↣Tx {n} {tt}
                            |                                    |
                            |                                    |
                      Ty ⟨ m , tt ⟩ ←--------------------- Ty ⟨ n , tt ⟩ ∋ t
                                        Ty ⟪ m≤n , e-tt ⟫_
        EQUIVALENTLY : 
                                      restr T x [ const-subst γx ] ⟪ m≤n , e-tt ⟫_
                      T ⟨ [ m , x ] , γx ⟩ ←--------------------------- T ⟨ [ n , x ] , γx ⟩
                            ↑                                                   ↑
        func Ty↣Tx {m} {tt} |                                                   | func Ty↣Tx {n} {tt}
                            |                                                   |
                            |                                                   |
                      T ⟨ [ m , y ] , γy ⟩ ←--------------------------- T ⟨ [ n , y ] , γy ⟩ ∋ t
                                        restr T y [ const-subst γy ] ⟪ m≤n , e-tt ⟫_

        RHS : restr T x [ const-subst γx ] ⟪ m≤n , e-tt ⟫ (func Ty↣Tx t) ≡ func Ty↣Tx {m} {tt} (restr T y [ const-subst γy ] ⟪ m≤n , e-tt ⟫ t)

        constantly-ctx Γ <at> x ⊢ restr T x
        ◇ ­⊢ restr T x [ const-subst γx ]
        const-subst γx : ◇ ⇒ (constantly-ctx Γ <at> x)
        
          restr T x [ const-subst γx ] ⟪ m≤n , e-tt ⟫ (func Ty↣Tx {n} t)
          -- {x = m} {y = n} {δy δx = tt} e-tt (func Ty↣Tx t)
        ≡⟨⟩
          restr T x ⟪ m≤n , proof-x ⟫ (func Ty↣Tx t)
              -- proof-x : (constantly-ctx Γ <at> x) ⟪ m≤n ⟫ γx ≡ γx 
              --         = constantly-ctx Γ ⟪ [ m≤n , hom-id V {x} ] ⟫ γx ≡ γx
              --         = Γ ⟪ hom-id V {x} ⟫ γx ≡ γx
        ≡⟨⟩
          T ⟪ [ m≤n , hom-id V {x} ] , proof-x ⟫ (func Ty↣Tx {n} {tt} t) 
        ≡⟨⟩
          T ⟪ [ m≤n , hom-id V {x} ] , proof-x ⟫ (T ⟪ [ ≤-refl {n} , g ] , eγ ⟫ t)
        ≡˘⟨ ty-comp T ⟩
          T ⟪ [ (≤-refl {n}) ∙ m≤n , g ∙ hom-id V {x} ] , strong-ctx-comp (constantly-ctx Γ) eγ proof-x ⟫ t
                -- strong-ctx-comp (constantly-ctx Γ) {f = hom-id V {x}} {g = g} {γy} {γx} {γx} eγ proof-x : constantly-ctx Γ ⟪ [ ≤-refl {n} ∙ m≤n , g ∙ hom-id V {x} ] ⟫ γy ≡ γx
                --      = Γ ⟪ g ∙ hom-id V {x} ⟫ γy ≡ γx 
        ≡⟨ ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idⁱ V ]) ⟩
          T ⟪ [ m≤n ∙ (≤-refl {m}) , hom-id V {y} ∙ g ] , strong-ctx-comp (constantly-ctx Γ) proof-y eγ ⟫ t
            -- strong-ctx-comp (constantly-ctx Γ) proof-y eγ ⟫ t : constantly-ctx Γ ⟪ [ m≤n ∙ (≤-refl {m}) , hom-id V {y} ∙ g ] ⟫ γy ≡ γx 
            -- = Γ ⟪ hom-id V {y} ∙ g ⟫ γy ≡ γx 
        ≡⟨ ty-comp T ⟩
          T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (T ⟪ [ m≤n , hom-id V {y} ] , proof-y ⟫ t)
        ≡⟨⟩
          T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (restr T y ⟪ m≤n , proof-y ⟫ t)
            -- proof-y : (constantly-ctx Γ <at> y) ⟪ m≤n ⟫ γy ≡ γy
            --         = constantly-ctx Γ ⟪ [ m≤n , hom-id V {y} ] ⟫ γy ≡ γy
            --         =  Γ ⟪ hom-id V {y} ⟫ γy ≡ γy
        ≡⟨⟩
          T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (restr T y [ const-subst γy ] ⟪ m≤n , e-tt ⟫ t)
        ≡⟨⟩
          func Ty↣Tx {m} {tt} (restr T y [ const-subst γy ] ⟪ m≤n , e-tt ⟫ t) ∎

        eγ : Γ ⟪ g ⟫ y ≡ x
        γx : Γ ⟨ x ⟩ = constantly-ctx Γ ⟨ [ m , x ] ⟩ regardless of m 
        γy : Γ ⟨ y ⟩ = constantly-ctx Γ ⟨ [ m , y ] ⟩ regardless of m 

          forever-ty T ⟪ g , eγ ⟫_ 
        : forever-ty T ⟨ y , γy ⟩ → forever-ty T ⟨ x , γx ⟩
        = Tm ◇ (restr T y [ const-subst γy ]) → Tm ◇ (restr T x [ const-subst γx ])

        RHS : 
          s : Tm ◇ (restr T x [ const-subst γx ])
          with s ⟨ m , tt ⟩' : T ⟨ [ m , x ] , γx ⟩ 
          given that t ⟨ m , tt ⟩' : T ⟨ [ m , y ] , γy ⟩ 

          T ⟪ [ ≤-refl {m} , g ] , proof = eγ ⟫_
          proof : constantly-ctx Γ ⟪ [ ≤-refl {m} , g ] ⟫ γy ≡ γx
                = Γ ⟪ g ⟫ γy ≡ γx
      -}
ty-cong (forever-ty T) e-hom = tm-≅-to-≡ (record { eq = λ _ → ty-cong T (×-≡,≡→≡ [ refl , e-hom ]) })
  {-
    t : forever-ty T ⟨ y , γy ⟩ = Tm ◇ (restr T y [ const-subst γy ])
    t ⟨ n , tt ⟩' : T ⟨ [ n , y ] , γy ⟩

    RHS : 
      forever-ty T ⟪ f , eγ ⟫ t ≡ forever-ty T ⟪ f' , eγ' ⟫ t
    Because `forever-ty T ⟨ _ , _ ⟩` contains semantic terms in ◇ @ ω, the above equality can be deduced from equivalence of terms. 
    What we need: 
      forever-ty T ⟪ f , eγ ⟫ t ≅ᵗᵐ forever-ty T ⟪ f' , eγ' ⟫ t
    More specifically, 
      eq {m} : λ tt → (forever-ty T ⟪ f , eγ ⟫ t) ⟨ m , tt ⟩' ≡ (forever-ty T ⟪ f' , eγ' ⟫ t) ⟨ m , tt ⟩' 
    = T ⟪ [ ≤-refl , f ] , eγ ⟫ (t ⟨ m , tt ⟩') ≡ T ⟪ [ ≤-refl , f' ] , eγ' ⟫ (t ⟨ m , tt ⟩')
    = ty-cong T (×-≡,≡→≡ [ refl , _ ])
  -}
ty-id (forever-ty T) = tm-≅-to-≡ (record { eq = λ _ → strong-ty-id T })
  {-
    t : forever-ty T ⟨ x , γ ⟩

    RHS : 
      forever-ty T ⟪ hom-id V , ctx-id Γ ⟫ t ≡ t
    Need : 
    ◇ ⊢ forever-ty T ⟪ hom-id V , ctx-id Γ ⟫ t ≅ᵗᵐ t : restr T [ const-subst γ ]

    eq {m} tt : (forever-ty T ⟪ hom-id V , ctx-id Γ ⟫ t) ⟨ m , tt ⟩ ≡ t ⟨ m , tt ⟩'
    = T ⟪ [ ≤-refl , hom-id V ] , ctx-id Γ ⟫ (t ⟨ m , tt ⟩') ≡ t ⟨ m , tt ⟩'
  -}
ty-comp (forever-ty T) = tm-≅-to-≡
  (record { eq = λ _ → trans (ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ])) (ty-comp T) })
  {-
    NEED : 
      forever-ty T ⟪ g ∙ f , strong-ctx-comp Γ eγ-zy eγ-yx ⟫ t ≡ᵗᵐ forever-ty T ⟪ f , eγ-yx ⟫ (forever-ty T ⟪ g , eγ-zy ⟫ t)
    eq {m} tt : (forever-ty T ⟪ [ ≤-refl , g ∙ f ] , strong-ctx-comp Γ eγ-zy eγ-yx ⟫ t) ⟨ m , tt ⟩' ≡ forever-ty T ⟪ [ ≤-refl , f ] , eγ-yx ⟫ (forever-ty T ⟪ [ ≤-refl , g ] , eγ-zy ⟫ t) ⟨ m , t ⟩'

      (forever-ty T ⟪ [ ≤-refl , g ∙ f ] , strong-ctx-comp Γ eγ-zy eγ-yx ⟫ t) ⟨ m , tt ⟩'
    ≡⟨⟩
      T ⟪ [ ≤-refl , g ∙ f ] , strong-ctx-comp Γ eγ-zy eγ-yx ⟫ (t ⟨ m , tt ⟩')
    ≡⟨ ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]) ⟩
      T ⟪ [ ≤-refl ∙ ≤-refl , g ∙ f ] , strong-ctx-comp Γ eγ-zy eγ-yx ⟫ (t ⟨ m , tt ⟩')
    ≡⟨ ty-comp T ⟩
    ≡⟨⟩
      T ⟪ [ ≤-refl , f ] , eγ-yx ⟫ (T ⟪ [ ≤-refl , g ] , eγ-zy ⟫ (t ⟨ m , tt ⟩'))
    ≡⟨⟩
      T ⟪ [ ≤-refl , f ] , eγ-yx ⟫ ((forever-ty T ⟪ [ ≤-refl , g ] , eγ-zy ⟫ t) ⟨ m , t ⟩')
    ≡⟨⟩
      forever-ty T ⟪ f , eγ-yx ⟫ (forever-ty T ⟪ g , eγ-zy ⟫ t) ⟨ m , t ⟩' 
  -}

module _ {T : Ty (constantly-ctx Γ)} where
  {-
    The action of `forever` on terms
    A term constructor @ V

    constantly-ctx Γ ⊢ t : T @ ω×V
    ------------------------------------
    Γ ⊢ forever-tm t : forever-ty T @ V
          forever-tm t ⟨ x , γ ⟩' : Tm ◇ (restr T x [ const-subst γ ]) @ ω
            forever-tm t ⟨ x , γ ⟩' ⟨ m , tt ⟩' : T ⟨ [ m , x ] , γ ⟩ = restr T x [ const-subst γ ] ⟨ m , tt ⟩
  -}
  forever-tm : Tm (constantly-ctx Γ) T → Tm Γ (forever-ty T)
  forever-tm t ⟨ x , γ ⟩' ⟨ m , tt ⟩' = t ⟨ [ m , x ] , γ ⟩'
  Tm.naturality (forever-tm t ⟨ x , γ ⟩') {m} {n} {γy = tt} {γx = tt} m≤n e-tt = Tm.naturality t [ m≤n , hom-id V {x} ] (trans (_⇒_.naturality (const-subst {Γ = Γ} γ) {f = m≤n}) (cong (func (const-subst {Γ = Γ} γ) {m}) e-tt))
    {- 
      The first two expressions defines the output term.
      Need to show `◇ @ ω ⊢ forever-tm t ⟨ x , γ ⟩' : Tm ◇ (restr T x [ const-subst γ ]) = forever-ty T ⟨ x , γ ⟩'` is natural. 
      
      e-tt : ◇ ⟪ m≤n ⟫ tt ≡ tt
      
      RHS : 
        restr T x [ const-subst γ ] ⟪ m≤n , e-tt ⟫ (forever-tm t ⟨ x , γ ⟩' ⟨ n , tt ⟩') ≡ forever-tm t ⟨ x , γ ⟩' ⟨ m , tt ⟩'
      
      new-proof : (constantly-ctx Γ <at> x) ⟪ m≤n ⟫ γ ≡ γ   
      new-proof = trans (_⇒_.naturality (const-subst {Γ = Γ} γ) {f = m≤n}) (cong (func (const-subst {Γ = Γ} γ) {m}) e-tt)

      proof : restr T x [ const-subst γ ] ⟪ m≤n , e-tt ⟫ (forever-tm t ⟨ x , γ ⟩' ⟨ n , tt ⟩') ≡ forever-tm t ⟨ x , γ ⟩' ⟨ m , tt ⟩'
      proof = 
        begin
          restr T x [ const-subst γ ] ⟪ m≤n , e-tt ⟫ (forever-tm t ⟨ x , γ ⟩' ⟨ n , tt ⟩')
        ≡⟨⟩
          restr T x ⟪ m≤n , new-proof ⟫ (forever-tm t ⟨ x , γ ⟩' ⟨ n , tt ⟩')
        ≡⟨⟩
          T ⟪ [ m≤n , hom-id V {x} ] , new-proof ⟫ (forever-tm t ⟨ x , γ ⟩' ⟨ n , tt ⟩')
        ≡⟨⟩
          T ⟪ [ m≤n , hom-id V {x} ] , new-proof ⟫ (t ⟨ [ n , x ] , γ ⟩')
        ≡⟨ Tm.naturality t [ m≤n , hom-id V {x} ] new-proof ⟩
          t ⟨ [ m , x ] , γ ⟩'
        ≡⟨⟩
          forever-tm t ⟨ x , γ ⟩' ⟨ m , tt ⟩' ∎
    -}
  Tm.naturality (forever-tm t) g eγ = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t [ ≤-refl , g ] eγ })
    {-
      This is a term constructor, so we need to prove `forever-tm t` is natural: 
        Tm.naturality (forever-tm t) {x} {y} {γy} {γx} {g : x → y} (eγ : Γ ⟪ g ⟫ γy ≡ γx) = ?
      where ? : forever-ty T ⟪ g , eγ ⟫ (forever-tm t ⟨ y , γy ⟩) ≡ forever-tm t ⟨ x , γx ⟩
      
      Both sides are terms in ◇ @ ω so we obtain a proof of `forever-ty T ⟪ g , eγ ⟫ (forever-tm t ⟨ y , γy ⟩') ≅ᵗᵐ forever-tm t ⟨ x , γx ⟩'` and then use `tm-≅-to-≡`. 
      ◇ @ ω ⊢ proof : forever-ty T ⟪ g , eγ ⟫ (forever-tm t ⟨ y , γy ⟩) ≅ᵗᵐ forever-tm t ⟨ x , γx ⟩'
      eq proof {k} tt = : forever-ty T ⟪ g , eγ ⟫ (forever-tm t ⟨ y , γy ⟩) ⟨ k , tt ⟩' ≡ forever-tm t ⟨ k , tt ⟩'
        begin 
          forever-ty T ⟪ g , eγ ⟫ (forever-tm t ⟨ y , γy ⟩) ⟨ k , tt ⟩'
        ≡⟨⟩
          convert-term Ty↣Tx (forever-tm t ⟨ y , γy ⟩) ⟨ k , tt ⟩'
        ≡⟨⟩
          func Ty↣Tx {k} {tt} (forever-tm t ⟨ y , γy ⟩ ⟨ k , tt ⟩')
        ≡⟨⟩
          T ⟪ [ ≤-refl {k} , g ] , eγ ⟫ (forever-tm t ⟨ y , γy ⟩ ⟨ k , tt ⟩')
        ≡⟨⟩
          T ⟪ [ ≤-refl {k} , g ] , eγ ⟫ (t ⟨ [ k , y ] , γy ⟩')
        ≡⟨ Tm.naturality t [ ≤-refl , g ] eγ ⟩
          t ⟨ [ k , x ] , γx ⟩'
        ≡⟨⟩ 
          forever-tm t ⟨ x , γx ⟩' ⟨ k , tt ⟩' ∎
        where open ≡-Reasoning
    -}

  {-
    The inverse of `forever-tm`

    Γ ⊢ t : forever-ty T @ V
    --------------------------------------------
    constantly-ctx Γ ⊢ unforever-tm t : T @ ω×V
  -}
  unforever-tm : Tm Γ (forever-ty T) → Tm (constantly-ctx Γ) T
  unforever-tm t ⟨ [ m , x ] , γ ⟩' = t ⟨ x , γ ⟩' ⟨ m , tt ⟩'
  Tm.naturality (unforever-tm t) {[ m , x ]} {[ n , y ]} {γy} {γx} [ m≤n , g ] eγ = 
    begin
      T ⟪ [ m≤n , g ] , eγ ⟫ (unforever-tm t ⟨ [ n , y ] , γy ⟩')
    ≡⟨⟩
      T ⟪ [ m≤n , g ] , eγ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩')
    ≡˘⟨ ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩
      T ⟪ [ (_∙_) ω m≤n (≤-refl {m}) , (_∙_) V (hom-id V {y}) g ] , strong-ctx-comp (constantly-ctx Γ) {[ ≤-refl {m} , g ]} {[ m≤n , hom-id V {y} ]} {γy} {γy} {γx} (ctx-id Γ) eγ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩')
    ≡⟨ ty-comp T ⟩
      T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (T ⟪ [ m≤n , hom-id V {y} ] , ctx-id Γ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩'))
    ≡⟨ cong (T ⟪ [ ≤-refl {m} , g ] , eγ ⟫_) (ty-cong T refl) ⟩
      T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (T ⟪ [ m≤n , hom-id V {y} ] , _ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩'))
    ≡⟨ cong (T ⟪ [ ≤-refl {m} , g ] , eγ ⟫_) (Tm.naturality (t ⟨ y , γy ⟩') {m} {n} {tt} {tt} m≤n refl) ⟩
      T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (t ⟨ y , γy ⟩' ⟨ m , tt ⟩')
    ≡⟨⟩
      T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (t ⟨ y , γy ⟩') ⟨ m , tt ⟩'
    ≡⟨ cong (_⟨ m , tt ⟩') (Tm.naturality t {x} {y} {γy} {γx} g eγ) ⟩
      t ⟨ x , γx ⟩' ⟨ m , tt ⟩'
    ≡⟨⟩ 
      unforever-tm t ⟨ [ m , x ] , γx ⟩' ∎
    where open ≡-Reasoning
    {-
      RHS : 
        Tm.naturality (unforever-tm t) {[ m , x ]} {[ n , y ]} {γy} {γx} [ m≤n , g ] (eγ : Γ ⟪ g ⟫ γy ≡ γx) 
      : T ⟪ [ m≤n , g ] , eγ ⟫ (unforever-tm t ⟨ [ n , y ] , γy ⟩') ≡ unforever-tm t ⟨ [ m , x ] , γx ⟩'
      = T ⟪ [ m≤n , g ] , eγ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩') ≡ t ⟨ x , γx ⟩' ⟨ m , tt ⟩'

      begin
        T ⟪ [ m≤n , g ] , eγ ⟫ (unforever-tm t ⟨ [ n , y ] , γy ⟩')
      ≡⟨⟩
        T ⟪ [ m≤n , g ] , eγ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩')
      ≡˘⟨ ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , hom-idˡ V ]) ⟩
        T ⟪ [ m≤n ∙ ≤-refl {m} , (hom-id V {y}) ∙ g ] , strong-ctx-comp (constantly-ctx Γ) {[ ≤-refl {m} , g ]} {[ m≤n , hom-id V {y} ]} {γy} {γy} {γx} (ctx-id (constantly-ctx Γ)) eγ ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩')
              -- strong-ctx-comp (constantly-ctx Γ) {[ ≤-refl {m} , g ]} {[ m≤n , hom-id V {y} ]} {γy} {γy} {γx} (ctx-id (constantly-ctx Γ)) eγ : `constantly-ctx Γ ⟪ [ m≤n ∙ ≤-refl {m} , (hom-id V {y}) ∙ g ] ⟫ γy ≡ γx` = `Γ ⟪ (hom-id V {y}) ∙ g ⟫ γy ≡ γx`
      ≡⟨ ty-comp T ⟩
        T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (T ⟪ [ m≤n , hom-id V {y} ] , ctx-id (constantly-ctx Γ) ⟫ (t ⟨ y , γy ⟩' ⟨ n , tt ⟩'))
      ≡⟨ cong (T ⟪ [ ≤-refl {m} , g ] , eγ ⟫_) (ty-cong T refl) ⟩
        T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (T ⟪ [ m≤n , hom-id V {y} ] , new-proof ⟫ (t ⟨ y , γn ⟩' ⟨ n , tt ⟩'))
      ≡⟨ cong (T ⟪ [ ≤-refl {m} , g ] , eγ ⟫_) (Tm.naturality (t ⟨ y , γn ⟩') {m} {n} {tt} {tt} m≤n e-tt) ⟩
        T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (t ⟨ y , γn ⟩' ⟨ m , tt ⟩')
      ≡⟨⟩
        T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (t ⟨ y , γy ⟩') ⟨ m , tt ⟩'
      ≡⟨ cong (_⟨ m , tt ⟩') (Tm.naturality t {x} {y} {γy} {γx} {g} eγ) ⟩
        t ⟨ x , γx ⟩' ⟨ m , tt ⟩'
      ≡⟨⟩ 
        unforever-tm t ⟨ [ m , x ] , γx ⟩' ∎
      where open ≡-Reasoning

        Tm.naturality t {x} {y} {γy} {γx} {g} eγ
      : forever-ty T ⟪ f , eγ ⟫ (t ⟨ y , γy ⟩') ≡ t ⟨ x , γx ⟩'
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (t ⟨ y , γy ⟩') ≡ t ⟨ x , γx ⟩'
      ◆ @ ω ⊢ t ⟨ y , γy ⟩' : Tm ◆ (restr T y [ const-subst γn ])
      t ⟨ y , γn ⟩' ⟨ n , tt ⟩' : T ⟨ [ n , y ] , γn ⟩
    -}

  forever-ty-β : (t : Tm (constantly-ctx Γ) T) → unforever-tm (forever-tm t) ≅ᵗᵐ t
  eq (forever-ty-β t) _ = refl

  forever-ty-η : (t : Tm Γ (forever-ty T)) → forever-tm (unforever-tm t) ≅ᵗᵐ t
  eq (forever-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

{-
  constantly-ctx Γ ⊢ T ≅ᵗʸ S @ ω×V
  ---------------------------------------
  Γ ⊢ forever-ty T ≅ᵗʸ forever-ty S @ V

  The action of `forever` on types respects equivalence of types.
-}
forever-ty-cong : {T : Ty (constantly-ctx Γ)} {S : Ty (constantly-ctx Γ)} →
                  T ≅ᵗʸ S → forever-ty T ≅ᵗʸ forever-ty S
-- from : forever-ty T ↣ forever-ty S
func (from (forever-ty-cong T=S)) {x} {γ} = ι⁻¹[ ty-subst-cong-ty (const-subst γ) (restr-cong T=S) ]_
  {-
      forever-ty T ⟨ x , γ ⟩ → forever-ty S ⟨ x , γ ⟩
    = Tm ◆ (restr T x [ const-subst γ ]) → Tm ◆ (restr S x [ const-subst γ ])
    = ι⁻¹[ proof : restr T x [ const-subst γ ] ≅ᵗʸ restr S x [ const-subst γ ] ]_
     
    proof = ty-subst-cong-ty (const-subst γ) (restr-cong T=S : restr T x ≅ᵗʸ restr S x)
  -}
_↣_.naturality (from (forever-ty-cong T=S)) = tm-≅-to-≡ (record { eq = λ _ → _↣_.naturality (from T=S) })
-- to : forever-ty S ↣ forever-ty T
func (to (forever-ty-cong T=S)) {x} {γ} = ι⁻¹[ ty-subst-cong-ty (const-subst γ) (restr-cong (≅ᵗʸ-sym T=S)) ]_
_↣_.naturality (to (forever-ty-cong T=S)) = tm-≅-to-≡ (record { eq = λ _ → _↣_.naturality (to T=S) })
eq (isoˡ (forever-ty-cong T=S)) {x} {γ} t = tm-≅-to-≡ (ι-symʳ (ty-subst-cong-ty (const-subst γ) (restr-cong T=S)) _)
eq (isoʳ (forever-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symˡ (ty-subst-cong-ty (const-subst _) (restr-cong T=S)) _)

module _ {T : Ty (constantly-ctx Γ)} where
  forever-tm-cong : {t s : Tm (constantly-ctx Γ) T} → t ≅ᵗᵐ s → forever-tm t ≅ᵗᵐ forever-tm s
  eq (forever-tm-cong t=s) γ = tm-≅-to-≡ (record { eq = λ _ → eq t=s γ })

  unforever-tm-cong : {t s : Tm Γ (forever-ty T)} → t ≅ᵗᵐ s → unforever-tm t ≅ᵗᵐ unforever-tm s
  eq (unforever-tm-cong t=s) γ = cong (λ - → - ⟨ _ , tt ⟩') (eq t=s γ)

module _ {T S : Ty (constantly-ctx Γ)} (T=S : T ≅ᵗʸ S) where
  forever-tm-ι : (s : Tm (constantly-ctx Γ) S) → ι[ forever-ty-cong T=S ] forever-tm s ≅ᵗᵐ forever-tm (ι[ T=S ] s)
  eq (forever-tm-ι s) γ = tm-≅-to-≡ (record { eq = λ _ → refl })

  unforever-tm-ι : (s : Tm Γ (forever-ty S)) → ι[ T=S ] unforever-tm s ≅ᵗᵐ unforever-tm (ι[ forever-ty-cong T=S ] s)
  eq (unforever-tm-ι s) _ = refl

{- 
  σ : Δ ⇒ Γ @ V
  constantly-ctx Γ ⊢ T @ ω×V      constantly-subst σ : constantly-ctx Δ ⇒ constantly-ctx Γ @ ω×V


  constantly-ctx Δ ⊢ T [ constantly-subst σ ] @ ω×V
  constantly-ctx Δ <at> x ⊢ restr (T [ constantly-subst σ ]) x @ ω
  const-subst δ : ◇ ⇒ (constantly-ctx Δ <at> x) @ ω   
  -------------------------------------------------------------
  ◇ ⊢ restr (T [ constantly-subst σ ]) x [ const-subst δ ] @ ω

  const-subst (func σ δ) : ◇ ⇒ (constantly-ctx Γ <at> (func σ δ)) @ ω
  constantly-ctx Γ <at> x ⊢ restr T x @ ω
  ----------------------------------------------
  ◇ ⊢ restr T x [ const-subst (func σ δ) ] @ ω

  WTS : 
    ◇ ⊢ restr (T [ constantly-subst σ ]) x [ const-subst δ ] ≅ᵗʸ restr T x [ const-subst (func σ δ) ] @ ω
-}
{- Original version
  ty-const-subst : (T : Ty (constantly-ctx Γ)) (σ : Δ ⇒ Γ) (δ : Δ ⟨ x ⟩) →
                  (T [ constantly-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
  ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (constantly-subst σ) (const-subst _))
                                  (ty-subst-cong-subst (const-subst-natural _ σ) T)
  ty-subst-comp T (constantly-subst σ) (const-subst _) : T [ constantly-subst σ ] [ const-subst _ ] ≅ᵗʸ T [ constantly-subst σ ⊚ const-subst _ ]
  ty-subst-cong-subst (const-subst-natural _ σ) T : T [ constantly-subst σ ⊚ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]

-}

ty-const-subst : {x : Ob V} → (T : Ty (constantly-ctx Γ)) (σ : Δ ⇒ Γ) (δ : Δ ⟨ x ⟩) →
                 restr (T [ constantly-subst σ ]) x [ const-subst δ ] ≅ᵗʸ restr T x [ const-subst (func σ δ) ]
func (from(ty-const-subst {x = x} T σ δ)) {m} {tt} = id {A = T ⟨ [ m , x ] , func σ δ ⟩}
  {-
    RHS : 
        restr (T [ constantly-subst σ ]) x [ const-subst δ ] ⟨ m , tt ⟩ → restr T x [ const-subst (func σ δ) ] ⟨ m , tt ⟩
      = restr (T [ constantly-subst σ ]) x ⟨ m , func (const-subst δ) tt ⟩ → restr T x ⟨ m , func (const-subst (func σ δ)) tt ⟩
      = restr (T [ constantly-subst σ ]) x ⟨ m , δ ⟩ → restr T x ⟨ m , func σ δ ⟩
      = T [ constantly-subst σ ] ⟨ [ m , x ] , δ ⟩ → T ⟨ [ m , x ] , func σ δ ⟩
      = T ⟨ [ m , x ] , func (constantly-subst σ) δ ⟩ → T ⟨ [ m , x ] , func σ δ ⟩
      = T ⟨ [ m , x ] , func σ {x} δ ⟩ → T ⟨ [ m , x ] , func σ δ ⟩
      = id {T ⟨ [ m , x ] , func σ δ ⟩}
  -}
_↣_.naturality (from(ty-const-subst {x} T σ δ)) {m} {n} {m≤n} {tt} {tt} {e-tt} {t} = ty-cong T refl
    {-
      RHS : 
        restr T x [ const-subst (func σ δ) ] ⟪ m≤n , e-tt ⟫ (id {A = T ⟨ [ n , x ] , func σ δ ⟩} t ) ≡ id {A = T ⟨ [ m , x ] , func σ δ ⟩} (restr (T [ constantly-subst σ ]) x [ const-subst δ ] ⟪ m≤n , e-tt ⟫ t)

        restr T x [ const-subst (func σ δ) ] ⟪ m≤n , e-tt ⟫ (id {A = T ⟨ [ n , x ] , func σ δ ⟩} t )
      ≡⟨⟩
        restr T x ⟪ m≤n , ty-subst-⟪_,_⟫-proof (const-subst (func σ δ)) m≤n tt tt e-tt ⟫ t
            -- ty-subst-⟪_,_⟫-proof (const-subst (func σ δ)) m≤n tt tt e-tt
            -- : (constantly-ctx Γ <at> x) ⟪ m≤n ⟫ (func (const-subst (func σ δ)) tt) ≡ (func (const-subst (func σ δ)) tt)
            -- = constantly-ctx Γ ⟪ [ m≤n , hom-id V {x} ] ⟫ (func σ δ) ≡ (func σ δ)
            -- = Γ ⟪ hom-id V {x} ⟫ (func σ δ) ≡ (func σ δ)
      ≡⟨⟩
        T ⟪ [ m≤n , hom-id V {x} ] , ty-subst-⟪_,_⟫-proof (const-subst (func σ δ)) m≤n tt tt e-tt ⟫ t
      ≡⟨ ty-cong T refl ⟩
        T ⟪ [ m≤n , hom-id V {x} ] , ty-subst-⟪_,_⟫-proof (constantly-subst σ) [ m≤n , hom-id V {x} ] δ δ (ty-subst-⟪_,_⟫-proof (const-subst δ) m≤n tt tt e-tt) ⟫ t
            -- ty-subst-⟪_,_⟫-proof (constantly-subst σ) [ m≤n , hom-id V {x} ] δ δ (ty-subst-⟪_,_⟫-proof (const-subst δ) m≤n tt tt e-tt)
            -- : constantly-ctx Γ ⟪ [ m≤n , hom-id V {x} ] ⟫ (func (constantly-subst σ) δ) ≡ (func (constantly-subst σ) δ)
            -- = Γ ⟪ hom-id V {x} ⟫ (func σ δ) ≡ func σ δ
      ≡⟨⟩
        T [ constantly-subst σ ] ⟪ [ m≤n , hom-id V {x} ] , ty-subst-⟪_,_⟫-proof (const-subst δ) m≤n tt tt e-tt ⟫ t
      ≡⟨⟩
        restr (T [ constantly-subst σ ]) x ⟪ m≤n , ty-subst-⟪_,_⟫-proof (const-subst δ) m≤n tt tt e-tt ⟫ t
            -- ty-subst-⟪_,_⟫-proof (const-subst δ) m≤n tt tt e-tt 
            -- : (constantly-ctx Δ ⟨at⟩ x) ⟪ m≤n ⟫ (func (const-subst δ) tt) ≡ func (const-subst δ) tt
            -- = constantly-ctx Δ ⟪ [ m≤n, hom-id V {x} ] ⟫ δ ≡ δ
            -- = Δ ⟪ hom-id V {x} ⟫ δ ≡ δ
      ≡⟨⟩
        restr (T [ constantly-subst σ ]) x [ const-subst δ ] ⟪ m≤n , e-tt ⟫ t
      ≡⟨⟩
        id {A = T ⟨ [ m , x ] , func σ δ ⟩} (restr (T [ constantly-subst σ ]) x [ const-subst δ ] ⟪ m≤n , e-tt ⟫ t) 
    -}
func (to(ty-const-subst T σ δ)) {m} = id {A = T ⟨ [ m , _ ] , func σ δ ⟩}
_↣_.naturality (to(ty-const-subst T σ δ)) = ty-cong T refl
eq (isoˡ (ty-const-subst T σ δ)) t = refl
eq (isoʳ(ty-const-subst T σ δ)) t = refl

{-
  σ : Δ ⇒ Γ @ V
  constantly-ctx Γ ⊢ T @ ω×V
  --------------------------------------------------
  constantly-ctx Δ ⊢ T [ constantly-subst σ ] @ ω×V

  Γ ⊢ forever-ty T @ V      Δ ⊢ forever-ty (T [ constantly-subst σ ]) @ V
  -------------------------------------------------------------------------
  Δ ⊢ (forever-ty T) [ σ ] ≅ᵗʸ forever-ty (T [ constantly-subst σ ]) @ V
-}
forever-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (constantly-ctx Γ)} → (forever-ty T) [ σ ] ≅ᵗʸ forever-ty (T [ constantly-subst σ ])
func (from (forever-ty-natural σ {T})) {γ = γ} = ι[ ty-const-subst T σ γ ]_
  {-
    γ : Δ ⟨ x ⟩

      (forever-ty T) [ σ ] ⟨ x , γ ⟩ → forever-ty (T [ constantly-subst σ ]) ⟨ x , γ ⟩
    = forever-ty T ⟨ x , func σ γ ⟩ → Tm ◇ (restr (T [ constantly-subst σ ]) x [ const-subst γ ])
    = Tm ◇ (restr T x [ const-subst (func σ γ) ]) → Tm ◇ (restr (T [ constantly-subst σ ]) x [ const-subst γ ])
    = ι[ ty-const-subst {x = x} T σ γ ]_
    ? : restr T x [ const-subst (func σ γ) ] ≅ᵗʸ restr (T [ constantly-subst σ ]) x [ const-subst γ ]
  -}
_↣_.naturality (from (forever-ty-natural σ {T})) = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
  {-
    {x} {y} {g} {γy : Δ ⟨ y ⟩} {γx : Δ ⟨ x ⟩} {eγ : Δ ⟪ g ⟫ γy ≡ γx} {t : (forever-ty T) [ σ ] ⟨ t , γy ⟩}
    RHS : 
      forever-ty (T [ constantly-subst σ ]) ⟪ g , eγ ⟫ (func {y} {γy} t) ≡ func {x} {γx} ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t)
    begin
      forever-ty (T [ constantly-subst σ ]) ⟪ g , eγ ⟫ (func {y} {γy} t)
    ≡⟨⟩
      forever-ty (T [ constantly-subst σ ]) ⟪ g , eγ ⟫ (ι[ ty-const-subst T σ γy ] t)
    ≡⟨⟩
      convert-term Ty↣Tx (ι[ ty-const-subst T σ γy ] t)
    ≡⟨⟩ ?
      ι[ ty-const-subst T σ γx ] ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t)
    ≡⟨⟩
      func {x} {γx} ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t)
    
    The above is equality two terms; need to first prove term equivalence.

    NEED :
      convert-term Ty↣Tx (ι[ ty-const-subst T σ γy ] t) ⟨ m , tt ⟩' ≡ ι[ ty-const-subst T σ γx ] ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t) ⟨ m , tt ⟩'
      = func (Ty↣Tx) ((ι[ ty-const-subst T σ γy ] t) ⟨ m , tt ⟩') ≡ convert-term (to (ty-const-subst T σ γx)) ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t) ⟨ m , tt ⟩'
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((ι[ ty-const-subst T σ γy ] t) ⟨ m , tt ⟩') ≡ func (to (ty-const-subst T σ γx)) ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t ⟨ m , tt ⟩')
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((convert-term (to (ty-const-subst T σ γy)) t) ⟨ m , tt ⟩') ≡ func (to (ty-const-subst T σ γx)) ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t ⟨ m , tt ⟩')
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((func (to (ty-const-subst T σ γy)) (t ⟨ m , tt ⟩')) ≡ func (to (ty-const-subst T σ γx)) ((forever-ty T) [ σ ] ⟪ g , eγ ⟫ t ⟨ m , tt ⟩')
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((func (to (ty-const-subst T σ γy)) (t ⟨ m , tt ⟩')) ≡ func (to (ty-const-subst T σ γx)) ((forever-ty T) ⟪ g , ty-subst-⟪_,_⟫-proof σ g (γy : Δ ⟨ y ⟩) (γx : Δ ⟨ x ⟩) eγ ⟫ t ⟨ m , tt ⟩')
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((func (to (ty-const-subst T σ γy)) (t ⟨ m , tt ⟩')) ≡ func (to (ty-const-subst T σ γx)) ((convert-term Ty↣Tx t) ⟨ m , tt ⟩')
            -- Ty↣Tx : restr T y [ const-subst γy ] ↣ restr T x [ const-subst γx ]
            -- from ⟪ g , ty-subst-⟪_,_⟫-proof σ g δy δx eγ ⟫ t ⟨ m , tt ⟩'
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((func (to (ty-const-subst T σ γy)) (t ⟨ m , tt ⟩')) ≡ func (to (ty-const-subst T σ γx)) (func Ty↣Tx (t ⟨ m , tt ⟩'))
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((func (to (ty-const-subst T σ γy)) (t ⟨ m , tt ⟩')) ≡ func (to (ty-const-subst T σ γx)) (T ⟪ [ ≤-refl {m} , g ] , ty-subst-⟪_,_⟫-proof σ g δy δx eγ ⟫ (t ⟨ m , tt ⟩'))
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ ((id (t ⟨ m , tt ⟩')) ≡ id (T ⟪ [ ≤-refl {m} , g ] , ty-subst-⟪_,_⟫-proof σ g δy δx eγ ⟫ (t ⟨ m , tt ⟩'))
      = T ⟪ [ ≤-refl {m} , g ] , eγ ⟫ (t ⟨ m , tt ⟩') ≡ T ⟪ [ ≤-refl {m} , g ] , ty-subst-⟪_,_⟫-proof σ g δy δx eγ ⟫ (t ⟨ m , tt ⟩')
      = ty-cong T refl
  -}
func (to (forever-ty-natural σ {T})) {γ = γ} = ι⁻¹[ ty-const-subst T σ γ ]_
-- todo: the remaining part of the def
_↣_.naturality (to (forever-ty-natural σ {T})) = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoˡ (forever-ty-natural σ {T})) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
eq (isoʳ (forever-ty-natural σ {T})) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)

instance
  forever-closed : {A : ClosedTy ω×V} {{_ : IsClosedNatural A}} → IsClosedNatural (forever-ty A)
  closed-natural {{forever-closed}} σ = ≅ᵗʸ-trans (forever-ty-natural σ) (forever-ty-cong (closed-natural (constantly-subst σ)))

module _ (σ : Δ ⇒ Γ) {T : Ty (constantly-ctx Γ)} where
  {-
    constantly-ctx Γ ⊢ t : T @ ω×V
    Γ ⊢ forever-tm t : forever-ty T @ V
    ---------------------------------------------------
    Δ ⊢ (forever-tm t) [ σ ]' : (forever-ty T) [ σ ] @ V
         (forever-tm t) [ σ ]' ⟨ x , γ ⟩' = forever-tm t ⟨ x , func σ γ ⟩'
                                          : forever-ty T ⟨ x , func σ γ ⟩
                                          = Tm ◇ (restr T x [ const-subst (func σ γ) ]) @ ω

    constantly-ctx Γ ⊢ t : T @ ω×V
    constantly-ctx Δ ⊢ t [ constantly-subst σ ]' : T [ constantly-subst σ ] @ ω×V
    ---------------------------------------------------------------------------------------
    Δ ⊢ forever-tm (t [ constantly-subst σ ]') : forever-ty (T [ constantly-subst σ ]) @ V
    Δ ⊢ (forever-ty T) [ σ ] ≅ᵗʸ forever-ty (T [ constantly-subst σ ]) @ V
    --------------------
    Δ ⊢ (forever-tm t) [ σ ]' ≅ᵗᵐ ι[ forever-ty-natural σ ] (forever-tm (t [ constantly-subst σ ]')) : (forever-ty T) [ σ ] @ V

    Δ ⊢ (forever-tm t) [ σ ]' ⟨ x , γ ⟩' : (forever-ty T) [ σ ]' ⟨ x , γ ⟩'
                                          = forever-ty T ⟨ x , func σ γ ⟩'
                                          = Tm ◇ (restr T x [ const-subst (func σ γ) ])
    ◇ ⊢ (forever-tm t) [ σ ]' ⟨ x , γ ⟩' : restr T x [ const-subst (func σ γ) ] @ ω
  -}
  forever-tm-natural : (t : Tm (constantly-ctx Γ) T) →
                       (forever-tm t) [ σ ]' ≅ᵗᵐ ι[ forever-ty-natural σ ] (forever-tm (t [ constantly-subst σ ]'))
  eq (forever-tm-natural t) γ = tm-≅-to-≡ (record { eq = λ _ → refl })
    {-
      γ : Δ ⟨ x ⟩
      eq (forever-tm-natural t) {x} γ : ((forever-tm t) [ σ ]') ⟨ x , γ ⟩' ≡ ι[ forever-ty-natural σ ] (forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩'
      Both sides are terms; need to show 
        ◇ ⊢ ψ : (forever-tm t) [ σ ]' ⟨ x , γ ⟩' ≅ᵗᵐ ι[ forever-ty-natural σ ] (forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩'

        eq ψ {m} tt
      : ((forever-tm t) [ σ ]' ⟨ x , γ ⟩') ⟨ m , tt ⟩' ≡ (ι[ forever-ty-natural σ ] (forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩') ⟨ m , tt ⟩'
        
        begin 
          
        : ◇ ⊢ (forever-tm t) [ σ ]' ⟨ x , γ ⟩' : restr T x [ const-subst (func σ γ) ] @ ω
          constantly-ctx Γ <at> x ⊢ restr T x @ ω
          ◇ ⊢ restr T x [ const-subst (func σ γ) ] @ ω
          ((forever-tm t) [ σ ]' ⟨ x , γ ⟩') ⟨ m , tt ⟩'
        ≡⟨⟩
          ((forever-tm t) ⟨ x , func σ γ ⟩') ⟨ m , tt ⟩'
        ≡⟨⟩
          t ⟨ [ m , x ] , func σ γ ⟩'
        ≡⟨⟩
          t ⟨ [ m , x ] , func (constantly-subst σ) γ ⟩'
        ≡⟨⟩
          (t [ constantly-subst σ ]') ⟨ [ m , x ] , γ ⟩'
        ≡⟨⟩
          (forever-tm (t [ constantly-subst σ ]') ⟨ x, γ ⟩') ⟨ m , tt ⟩'
        ≡⟨⟩
          func (from (ty-const-subst T σ γ)) (((forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩') ⟨ m , tt ⟩')
        ≡⟨⟩
          func (to (≅ᵗʸ-sym (ty-const-subst T σ γ))) (((forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩') ⟨ m , tt ⟩')
        ≡⟨⟩
          (convert-term (to (≅ᵗʸ-sym (ty-const-subst T σ γ))) ((forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩'))  
        ≡⟨⟩
          (ι[ ≅ᵗʸ-sym (ty-const-subst T σ γ) ] ((forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩')) ⟨ m , tt ⟩'
        ≡⟨⟩
          (ι⁻¹[ ty-const-subst T σ γ ] ((forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩')) ⟨ m , tt ⟩'
        ≡⟨⟩
          (func (to (forever-ty-natural σ)) ((forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩')) ⟨ m , tt ⟩'
        ≡⟨⟩
          ((convert-term (to (forever-ty-natural σ)) (forever-tm (t [ constantly-subst σ ]'))) ⟨ x, γ ⟩') ⟨ m , tt ⟩'
        ≡⟨⟩
          (ι[ forever-ty-natural σ ] (forever-tm (t [ constantly-subst σ ]')) ⟨ x, γ ⟩') ⟨ m , tt ⟩'

        ty-const-subst T σ γ : ◇ ⊢ restr (T [ constantly-subst σ ]) x [ const-subst δ ] ≅ᵗʸ restr T x [ const-subst (func σ δ) ]
    -}

  unforever-tm-natural : (t : Tm Γ (forever-ty T)) →
                         (unforever-tm t) [ constantly-subst σ ]' ≅ᵗᵐ unforever-tm (ι⁻¹[ forever-ty-natural σ ] (t [ σ ]'))
  eq (unforever-tm-natural t) _ = refl