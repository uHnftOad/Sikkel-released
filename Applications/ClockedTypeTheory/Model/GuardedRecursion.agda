module Applications.ClockedTypeTheory.Model.GuardedRecursion where

open import Data.Nat
open import Data.Nat.Properties
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.Functor
open import Model.Modality
open import Model.CwF-Structure
open import Model.CwF-Structure.LiftingFunctors.Modality
open import Model.Type.Function

open BaseCategory


--------------------------------------------------
-- The `later` modality and its interaction with the unit modality

later : Modality ω ω
later = fun-to-mod ω-suc

id-functor→ω-suc : NatTransf id-functor ω-suc
transf-op id-functor→ω-suc n = n≤1+n n
naturality id-functor→ω-suc = ≤-irrelevant _ _

𝟙≤later : TwoCell 𝟙 later
𝟙≤later = (NatTransf-to-TwoCell id-functor→ω-suc) ⓣ-vert (≅ᵐ-to-2-cell (≅ᵐ-sym (fun-to-mod-id {ω})))

-- The löb primitive
◄ : Ctx ω → Ctx ω
◄ = lock later

from-earlier : (Γ : Ctx ω) → ◄ Γ ⇒ Γ
from-earlier Γ = transf-op (transf 𝟙≤later) Γ

ctx-m≤1+n : {m n : Ob ω} (Γ : Ctx ω) {m≤n : m ≤ n} {γ : Γ ⟨ suc n ⟩} →
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n Γ {γ = γ} = trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _)) (ctx-comp Γ))

{- The `from-earlier` defined above is the same as the `from-earlier` defined in the original implementation of guarded recursion. 

  from-earlier-orig : (Γ : Ctx ω) → ◄ Γ ⇒ Γ
  func (from-earlier-orig Γ) {n} = Γ ⟪ n≤1+n n ⟫_
  naturality (from-earlier-orig Γ) = ctx-m≤1+n Γ

  from-earlier-orig=from-earlier : (Γ : Ctx ω) → from-earlier-orig Γ ≅ˢ from-earlier Γ
  eq (from-earlier-orig=from-earlier Γ) _ = refl
-}

module _ {Γ : Ctx ω} where
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
  ◄-cancel : {n : Ob ω} → ◄ (𝕪 (suc n)) ≅ᶜ 𝕪 n
  func (from ◄-cancel) m+1≤n+1 = ≤-pred m+1≤n+1
  naturality (from ◄-cancel) = ≤-irrelevant _ _
  func (to ◄-cancel) m≤n = s≤s m≤n
  naturality (to ◄-cancel) = ≤-irrelevant _ _
  eq (isoˡ ◄-cancel) m+1≤n+1 = ≤-irrelevant _ _
  eq (isoʳ ◄-cancel) m≤n = ≤-irrelevant _ _

  ⇋ : {n : Ob ω} {γ : Γ ⟨ suc n ⟩} {T : Ty Γ} → 
      T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ] [ to ◄-cancel ] ⟨ n , ≤-refl {n} ⟩ →
      Tm (𝕪 n) (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ] [ to ◄-cancel ])
  ⇋ {γ = γ} {T} t ⟨ _ , m≤n ⟩' = T ⟪ m≤n , trans (cong (Γ ⟪ m≤n ⟫_) (trans (sym (ctx-comp Γ)) (cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _)))) (ctx-m≤1+n Γ) ⟫ t
  naturality (⇋ {T = T} _) _ _ = trans (sym (ty-comp T)) (ty-cong T (≤-irrelevant _ _))

  null : ∀ {γ} {T : Ty Γ} → Tm (◄ (𝕪 zero)) (T [ from-earlier Γ ] [ 𝝶 ω-suc γ ])
  null ⟨ zero , () ⟩'
  null ⟨ suc n , () ⟩'

  löb : (T : Ty Γ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
  löb T f = MkTm tm nat
    where
      tm : (n : Ob ω) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
      tm zero γ = f €⟨ zero , γ ⟩ null
      -- tm (suc n) γ = f €⟨ suc n , γ ⟩ (ι⁻¹[ iso ] (ιc[ ◄-cancel ]' tm'))
      --   where
      --     tm' : Tm (𝕪 n) (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ] [ to ◄-cancel ])
      --     tm' = ⇋ {γ = γ} (tm n (Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ ≤-refl ⟫ γ)))

      --     iso : T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ] [ to ◄-cancel ] [ from ◄-cancel ] ≅ᵗʸ T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ]
          -- iso = ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ]) _ _) 
          --      (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ])) 
          --                 (ty-subst-id (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ])))
      tm (suc n) γ = f €⟨ suc n , γ ⟩ 
                    (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ]) _ _) 
                         (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ])) 
                                    (ty-subst-id (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ]))) ] 
                      (ιc[ ◄-cancel ]' ⇋ (tm n (Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ ≤-refl ⟫ γ)))))

      open ≡-Reasoning
      nat : {m n : Ob ω} {γₙ : Γ ⟨ n ⟩} {γₘ : Γ ⟨ m ⟩} (m≤n : m ≤ n) (eγ : Γ ⟪ m≤n ⟫ γₙ ≡ γₘ) →
            T ⟪ m≤n , eγ ⟫ tm n γₙ ≡ tm m γₘ
      nat {zero} {zero} {γₙ} {γₘ} z≤n eγ =
        begin
          T ⟪ z≤n , eγ ⟫
            f €⟨ zero , γₙ ⟩ null
        ≡⟨ €-natural f ⟩
          f €⟨ zero , γₘ ⟩
            (▻' T ⟪ z≤n , eγ ⟫ null)
        ≡⟨ cong (f €⟨ zero , γₘ ⟩_) (tm-≅-to-≡ (record { eq = λ () })) ⟩
          f €⟨ zero , γₘ ⟩ null ∎
      nat {zero} {suc n} {γₘ = γₘ} _ _ = trans (€-natural f) (cong (f €⟨ zero , γₘ ⟩_) (tm-≅-to-≡ (record { eq = λ () })))
      nat {suc m} {suc n} {γₙ} {γₘ} (s≤s m≤n) eγ = trans (€-natural f) (cong (f €⟨ suc m , γₘ ⟩_) (tm-≅-to-≡ iso))
        where
          iso : ▻ (T [ from-earlier Γ ]) ⟪ s≤s m≤n , eγ ⟫ 
                    (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp ((T [ from-earlier Γ ]) [ 𝝶 ω-suc γₙ ]) (to ◄-cancel) (from ◄-cancel)) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) ((T [ from-earlier Γ ]) [ 𝝶 ω-suc γₙ ])) (ty-subst-id ((T [ from-earlier Γ ]) [ 𝝶 ω-suc γₙ ]))) ] 
                    (ιc[ ◄-cancel ]' ⇋ (tm n (Γ ⟪ n≤1+n n ⟫ (Γ ⟪ ≤-refl ⟫ γₙ))))) 
                    ≅ᵗᵐ
                  ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp ((T [ from-earlier Γ ]) [ 𝝶 ω-suc γₘ ]) (to ◄-cancel) (from ◄-cancel)) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) ((T [ from-earlier Γ ]) [ 𝝶 ω-suc γₘ ])) (ty-subst-id ((T [ from-earlier Γ ]) [ 𝝶 ω-suc γₘ ]))) ] 
                  (ιc[ ◄-cancel ]' ⇋ (tm m (Γ ⟪ n≤1+n m ⟫ (Γ ⟪ ≤-refl ⟫ γₘ))))
          eq iso (s≤s k≤m) =
            begin
              T ⟪ ≤-refl , _ ⟫
                T ⟪ ≤-refl , _ ⟫
                  T ⟪ ≤-pred (≤-trans (s≤s k≤m) (s≤s m≤n)) , _ ⟫ (tm n (Γ ⟪ n≤1+n n ⟫ (Γ ⟪ ≤-refl ⟫ γₙ)))
            ≡⟨ sym (ty-comp T) ⟩
              T ⟪ ≤-trans ≤-refl ≤-refl , _ ⟫
                T ⟪ ≤-pred (≤-trans (s≤s k≤m) (s≤s m≤n)) , _ ⟫ 
                  tm n (Γ ⟪ n≤1+n n ⟫ (Γ ⟪ ≤-refl ⟫ γₙ))
            ≡⟨ sym (ty-comp T) ⟩
              T ⟪ ≤-trans (≤-trans ≤-refl ≤-refl) (≤-pred (≤-trans (s≤s k≤m) (s≤s m≤n))) , _ ⟫ 
                tm n (Γ ⟪ n≤1+n n ⟫ (Γ ⟪ ≤-refl ⟫ γₙ))
            ≡⟨ ty-cong T (≤-irrelevant _ _) ⟩
              T ⟪ ≤-trans (≤-trans ≤-refl k≤m) (m≤n) , _ ⟫
                tm n (Γ ⟪ n≤1+n n ⟫ (Γ ⟪ ≤-refl ⟫ γₙ))
            ≡⟨ ty-comp T ⟩
              T ⟪ ≤-trans ≤-refl k≤m , _ ⟫
                T ⟪ m≤n , _ ⟫
                  tm n (Γ ⟪ n≤1+n n ⟫ (Γ ⟪ ≤-refl ⟫ γₙ))
            ≡⟨ cong (T ⟪ ≤-trans ≤-refl k≤m , _ ⟫_) (nat m≤n (trans (cong (Γ ⟪ m≤n ⟫_) (sym (ctx-comp Γ))) (trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γₙ) (≤-irrelevant _ _)) (trans (ctx-comp Γ) (trans (cong (Γ ⟪ n≤1+n m ⟫_) (ctx-comp Γ)) (cong (Γ ⟪ n≤1+n m ⟫_ ∘ Γ ⟪ ≤-refl ⟫_) eγ))))))) ⟩
              T ⟪ ≤-trans ≤-refl k≤m , _ ⟫
                tm m (Γ ⟪ n≤1+n m ⟫ (Γ ⟪ ≤-refl ⟫ γₘ))
            ≡⟨ ty-comp T ⟩
              T ⟪ ≤-refl , _ ⟫
                T ⟪ k≤m , _ ⟫
                  tm m (Γ ⟪ n≤1+n m ⟫ (Γ ⟪ ≤-refl ⟫ γₘ)) ∎

  löb' : (T : Ty Γ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
  löb' T f = löb T (lam (▻' T) f)

  löb[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻' T) (T [ π ]) → Tm Γ T
  löb[_∈▻'_]_ v = löb'

  löb-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) → app f (next' (löb T f)) ≅ᵗᵐ löb T f
  eq (löb-is-fixpoint {T} f) {zero} γ = cong (f €⟨ zero , γ ⟩_) (tm-≅-to-≡ (record { eq = λ () }))
  eq (löb-is-fixpoint {T} f) {suc n} γ = cong (f €⟨ suc n , γ ⟩_) (tm-≅-to-≡ iso)
    where
      open ≡-Reasoning
      iso : next' (löb T f) ⟨ suc n , γ ⟩'
              ≅ᵗᵐ 
            ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ]) _ _) 
                  (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄-cancel) (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ])) 
                            (ty-subst-id (T [ from-earlier Γ ] [ 𝝶 ω-suc {Γ} γ ]))) ] 
              (ιc[ ◄-cancel ]' ⇋ ((löb T f) ⟨ n , Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩'))
      eq iso {k} k+1≤n+1 =
        begin
          (löb T f) ⟨ k , Γ ⟪ n≤1+n k ⟫ (Γ ⟪ k+1≤n+1 ⟫ γ) ⟩'
        ≡⟨ sym (naturality (löb T f) (≤-trans ≤-refl (≤-pred k+1≤n+1)) (trans (cong (Γ ⟪ ≤-trans ≤-refl (≤-pred k+1≤n+1) ⟫_) (sym (ctx-comp Γ))) (trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _)) (ctx-comp Γ))))) ⟩
          T ⟪ ≤-trans ≤-refl (≤-pred k+1≤n+1) , _ ⟫
            (löb T f) ⟨ n , Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩'
        ≡⟨ ty-cong T refl ⟩
          T ⟪ ≤-trans ≤-refl (≤-pred k+1≤n+1) , _ ⟫
            (löb T f) ⟨ n , Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩'
        ≡⟨ ty-comp T ⟩
          T ⟪ ≤-refl , _ ⟫
            (T ⟪ ≤-pred k+1≤n+1 , _ ⟫ 
              (löb T f) ⟨ n , Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩') ∎
  
  -- FIXME: 
  fixpoint-unique : {T : Ty Γ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
                    app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
  eq (fixpoint-unique f _ _ t-fix s-fix) {zero} γ = trans (sym (eq t-fix γ)) (trans (cong (f €⟨ zero , γ ⟩_) (tm-≅-to-≡ (record { eq = λ () }))) (eq s-fix γ))
  eq (fixpoint-unique f t s t-fix s-fix) {suc n} γ =
    begin
      t ⟨ suc n , γ ⟩'
    ≡˘⟨ eq t-fix γ ⟩
      f €⟨ suc n , γ ⟩ (t [ _ ]' [ _ ]')
    ≡⟨ cong (f €⟨ suc n , γ ⟩_) (tm-≅-to-≡ (record { eq = λ {k} h → eq (fixpoint-unique f t s t-fix s-fix) {k} (func (from-earlier Γ) (func (𝝶 ω-suc {Γ} γ) h)) })) ⟩
      f €⟨ suc n , γ ⟩ (s [ _ ]' [ _ ]')
    ≡⟨ eq s-fix γ ⟩
      s ⟨ suc n , γ ⟩' ∎
    where open ≡-Reasoning

  -- ▻ is an applicative functor
  _⟨$⟩_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T) → Tm Γ (▻ S)
  f ⟨$⟩ t = next (app f (prev t))

  _⊛_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
  f ⊛ t = prev f ⟨$⟩ t


--------------------------------------------------
-- The `forever` modality and its interaction with the `later` modality

forever : Modality ω ★
forever = fun-to-mod 𝒵

𝒵∘ω-suc=𝒵 : 𝒵 ∘ᶠ ω-suc ≅ᶠ 𝒵
𝒵∘ω-suc=𝒵 = 𝒵∘functor=𝒵 ω-suc

forever-later : forever ⓜ later ≅ᵐ forever
forever-later = ≅ᵐ-trans (≅ᵐ-sym fun-to-mod-comp) (fun-to-mod-cong 𝒵∘ω-suc=𝒵)

forever-later'-ty : {Γ : Ctx ★} (T : Ty (Γ ,lock⟨ forever ⟩)) → ⟨ forever ∣ ▻' T ⟩ ≅ᵗʸ ⟨ forever ∣ T ⟩
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

constantly : Modality ★ ω
constantly = fun-to-mod 𝒬

𝒵∘𝒬=id : 𝒵 ∘ᶠ 𝒬 ≅ᶠ id-functor {★}
𝒵∘𝒬=id = transᶠ (𝒵∘functor=𝒵 𝒬) 𝒵-id

forever-constantly : forever ⓜ constantly ≅ᵐ 𝟙
forever-constantly =
  begin
    forever ⓜ constantly
  ≅⟨ ≅ᵐ-sym fun-to-mod-comp ⟩
    fun-to-mod (𝒵 ∘ᶠ 𝒬)
  ≅⟨ fun-to-mod-cong 𝒵∘𝒬=id ⟩
    fun-to-mod id-functor
  ≅⟨ fun-to-mod-id ⟩
    𝟙 ∎
  where open ≅ᵐ-Reasoning

-- TODO: 
-- constantly∘forever≤𝟙 : TwoCell (constantly ⓜ forever) 𝟙
-- transf-op (transf constantly∘forever≤𝟙) = to-constantly-now-ctx
-- CtxNatTransf.naturality (transf constantly∘forever≤𝟙) = to-constantly-now-ctx-natural

-- from-constantly-forever-ty : {Γ : Ctx ω} {T : Ty (constantly-ctx (now Γ))} →
--                              Tm Γ (constantly-ty (forever-ty T)) → Tm Γ (T [ to-constantly-now-ctx Γ ])
-- from-constantly-forever-ty {Γ = Γ} t = unforever-tm (unconstantly-tm t) [ to-constantly-now-ctx Γ ]'
