module Applications.ClockedTypeTheory.Model.Modalities where

open import Data.Nat
open import Data.Nat.Properties
open import Data.String using (String)

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injectiveˡ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.Functor
open import Model.Modality
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.CwF-Structure.LiftingFunctors.Modality

import Applications.ClockedTypeTheory.Model.Temp ★ as M★
import Applications.ClockedTypeTheory.Model.Temp ω as Mω

open BaseCategory

private
  ★×★ : BaseCategory
  ★×★ = ★ ⊗ ★

  ω×★ : BaseCategory
  ω×★ = ω ⊗ ★

  ω×ω : BaseCategory
  ω×ω = ω ⊗ ω

  variable
    m n k r : Ob ω
  
open BaseCategory


--------------------------------------------------
-- Modalities between ★×★ and ω×★ and their interactions

later₀ : Modality ω×★ ω×★
later₀ = M★.later

◄₀ = M★.◄

𝝶-later₀ : {Γ : Ctx ω×★} {d : Ob ω×★} → Γ ⟨ d ⟩ → ◄₀ (𝕪 d) ⇒ ◄₀ Γ
𝝶-later₀ = M★.𝝶-later

from-earlier₀ : (Γ : Ctx ω×★) → ◄₀ Γ ⇒ Γ
from-earlier₀ = M★.from-earlier

module _ {Γ : Ctx ω×★} where
  ▻₀ : Ty (◄₀ Γ) → Ty Γ
  ▻₀ = M★.▻

  ▻₀' : Ty Γ → Ty Γ
  ▻₀' = M★.▻'

  next₀' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻₀' T)
  next₀' = M★.next'

  ◄₀-cancel : ◄₀ (𝕪 [ suc n , _ ]) ≅ᶜ 𝕪 [ n , _ ]
  ◄₀-cancel = M★.◄-cancel {Γ}

  ⇋₀ : {γ : Γ ⟨ [ suc n , _ ] ⟩} {T : Ty Γ} → 
      T [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ ] [ to ◄₀-cancel ] ⟨ [ n , _ ] , [ ≤-refl , _ ] ⟩ →
      Tm (𝕪 [ n , _ ]) (T [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ ] [ to ◄₀-cancel ])
  ⇋₀ = M★.⇋

  null₀ : ∀ {γ} {T : Ty Γ} → Tm (◄₀ (𝕪 [ zero , _ ])) (T [ from-earlier₀ Γ ] [ 𝝶 M★.ω-suc×id γ ])
  null₀ = M★.null

  löb₀ : (T : Ty Γ) → Tm Γ (▻₀' T ⇛ T) → Tm Γ T
  löb₀ = M★.löb

  löb₀' : (T : Ty Γ) → Tm (Γ ,, ▻₀' T) (T [ π ]) → Tm Γ T
  löb₀' = M★.löb'

  löb₀[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻₀' T) (T [ π ]) → Tm Γ T
  löb₀[_∈▻'_]_ = M★.löb[_∈▻'_]_

  löb₀-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻₀' T ⇛ T)) → app f (next₀' (löb₀ T f)) ≅ᵗᵐ löb₀ T f
  löb₀-is-fixpoint = M★.löb-is-fixpoint

  _⟨$⟩₀_ : {T S : Ty (◄₀ Γ)} → Tm (◄₀ Γ) (T ⇛ S) → Tm Γ (▻₀ T) → Tm Γ (▻₀ S)
  _⟨$⟩₀_ = M★._⟨$⟩_

  _⊛₀_ : {T S : Ty (◄₀ Γ)} → Tm Γ (▻₀ (T ⇛ S)) → Tm Γ (▻₀ T) → Tm Γ (▻₀ S)
  _⊛₀_ = M★._⊛_

𝟙≤later₀ : TwoCell 𝟙 later₀
𝟙≤later₀ = M★.𝟙≤later

forever₀ : Modality ω×★ ★×★
forever₀ = M★.forever

constantly-ctx₀ = M★.constantly-ctx

𝝶-forever₀ : {Γ : Ctx ★×★} {d : Ob ★×★} → Γ ⟨ d ⟩ → (𝕪 d) ,lock⟨ forever₀ ⟩ ⇒ Γ ,lock⟨ forever₀ ⟩
𝝶-forever₀ = M★.𝝶-forever

forever₀-later₀ : forever₀ ⓜ later₀ ≅ᵐ forever₀
forever₀-later₀ = M★.forever-later

forever₀-later₀'-ty : {Γ : Ctx ★×★} (T : Ty (Γ ,lock⟨ forever₀ ⟩)) → ⟨ forever₀ ∣ ▻₀' T ⟩ ≅ᵗʸ ⟨ forever₀ ∣ T ⟩
forever₀-later₀'-ty = M★.forever-later'-ty

constantly₀ : Modality ★×★ ω×★
constantly₀ = M★.constantly

now₀ = M★.now

𝝶-constantly₀ : {Γ : Ctx ω×★} {d : Ob ω×★} → Γ ⟨ d ⟩ → (𝕪 d) ,lock⟨ constantly₀ ⟩ ⇒ Γ ,lock⟨ constantly₀ ⟩
𝝶-constantly₀ = M★.𝝶-constantly

forever₀-constantly₀ : forever₀ ⓜ constantly₀ ≅ᵐ 𝟙
forever₀-constantly₀ = M★.forever-constantly

now₀-constantly₀-ctx-intro : {T : ClosedTy ★×★} {{_ : IsClosedNatural T}} {Γ : Ctx ★×★} →
                             Tm Γ T → Tm (lock constantly₀ (lock forever₀ Γ)) T
now₀-constantly₀-ctx-intro {T} = M★.now-constantly-ctx-intro {T}

to-constantly₀-now₀-ctx : (Γ : Ctx ω×★) → (Γ ⇒ lock forever₀ (lock constantly₀ Γ))
to-constantly₀-now₀-ctx = M★.to-constantly-now-ctx

from-constantly₀-forever₀-ty : {Γ : Ctx ω×★} {T : Ty (lock forever₀ (lock constantly₀ Γ))} →
                               Tm Γ ⟨ constantly₀ ∣ ⟨ forever₀ ∣ T ⟩ ⟩ → Tm Γ (T [ to-constantly₀-now₀-ctx Γ ])
from-constantly₀-forever₀-ty = M★.from-constantly-forever-ty

constantly₀∘forever₀≤𝟙 : TwoCell (constantly₀ ⓜ forever₀) 𝟙
constantly₀∘forever₀≤𝟙 = M★.constantly∘forever≤𝟙

--------------------------------------------------
-- Modalities between ω×★ and ω×ω and their interactions

-- This later modality acts on the left ω of ω×ω only. 
later₁ : Modality ω×ω ω×ω
later₁ = Mω.later

◄₁ = Mω.◄

𝝶-later₁ : {Γ : Ctx ω×ω} {d : Ob ω×ω} → Γ ⟨ d ⟩ → ◄₁ (𝕪 d) ⇒ ◄₁ Γ
𝝶-later₁ = Mω.𝝶-later

from-earlier₁ : (Γ : Ctx ω×ω) → ◄₁ Γ ⇒ Γ
from-earlier₁ = Mω.from-earlier

module _ {Γ : Ctx ω×ω} where
  ▻₁ : Ty (◄₁ Γ) → Ty Γ
  ▻₁ = Mω.▻

  ▻₁' : Ty Γ → Ty Γ
  ▻₁' = Mω.▻'

  next₁' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻₁' T)
  next₁' = Mω.next'

  ◄₁-cancel : ◄₁ (𝕪 [ suc n , r ]) ≅ᶜ 𝕪 [ n , r ]
  ◄₁-cancel = Mω.◄-cancel {Γ}

  ⇋₁ : {γ : Γ ⟨ [ suc n , r ] ⟩} {T : Ty Γ} → 
      T [ from-earlier₁ Γ ] [ 𝝶-later₁ {Γ} γ ] [ to ◄₁-cancel ] ⟨ [ n , r ] , [ ≤-refl , ≤-refl ] ⟩ →
      Tm (𝕪 [ n , r ]) (T [ from-earlier₁ Γ ] [ 𝝶-later₁ {Γ} γ ] [ to ◄₁-cancel ])
  ⇋₁ = Mω.⇋

  null₁ : ∀ {γ} {T : Ty Γ} → Tm (◄₁ (𝕪 [ zero , k ])) (T [ from-earlier₁ Γ ] [ 𝝶 Mω.ω-suc×id γ ])
  null₁ = Mω.null

  löb₁ : (T : Ty Γ) → Tm Γ (▻₁' T ⇛ T) → Tm Γ T
  löb₁ = Mω.löb

  löb₁' : (T : Ty Γ) → Tm (Γ ,, ▻₁' T) (T [ π ]) → Tm Γ T
  löb₁' = Mω.löb'

  löb₁[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻₁' T) (T [ π ]) → Tm Γ T
  löb₁[_∈▻'_]_ = Mω.löb[_∈▻'_]_

  löb₁-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻₁' T ⇛ T)) → app f (next₁' (löb₁ T f)) ≅ᵗᵐ löb₁ T f
  löb₁-is-fixpoint = Mω.löb-is-fixpoint

  _⟨$⟩₁_ : {T S : Ty (◄₁ Γ)} → Tm (◄₁ Γ) (T ⇛ S) → Tm Γ (▻₁ T) → Tm Γ (▻₁ S)
  _⟨$⟩₁_ = Mω._⟨$⟩_

  _⊛₁_ : {T S : Ty (◄₁ Γ)} → Tm Γ (▻₁ (T ⇛ S)) → Tm Γ (▻₁ T) → Tm Γ (▻₁ S)
  _⊛₁_ = Mω._⊛_

𝟙≤later₁ : TwoCell 𝟙 later₁
𝟙≤later₁ = Mω.𝟙≤later

-- This later modality acts on the right ω of ω×ω only. 
id×ω-suc : Functor ω×ω ω×ω
id×ω-suc = id-functor {ω} ⊗ᶠ ω-suc

later₂ : Modality ω×ω ω×ω
later₂ = fun-to-mod id×ω-suc

◄₂ : Ctx ω×ω → Ctx ω×ω
◄₂ = lock later₂

𝝶-later₂ : {Γ : Ctx ω×ω} {d : Ob ω×ω} → Γ ⟨ d ⟩ → ◄₂ (𝕪 d) ⇒ ◄₂ Γ
𝝶-later₂ = 𝝶 id×ω-suc

ctx-m≤1+nʳ : (Γ : Ctx ω×ω) {m≤n : m ≤ n} {k≤r : k ≤ r} {γ : Γ ⟨ [ r , suc n ] ⟩} →
             Γ ⟪ [ k≤r , m≤n ] ⟫ (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ γ) 
               ≡ 
             Γ ⟪ [ ≤-refl , n≤1+n m ] ⟫ (Γ ⟪ [ k≤r , s≤s m≤n ] ⟫ γ)
ctx-m≤1+nʳ Γ {γ = γ} = trans (sym (ctx-comp Γ)) 
                      (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , ≤-irrelevant _ _ ])) 
                      (trans (sym (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ]))) 
                             (ctx-comp Γ)))

from-earlier₂ : (Γ : Ctx ω×ω) → ◄₂ Γ ⇒ Γ
func (from-earlier₂ Γ) {[ _ , n ]} = Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫_
naturality (from-earlier₂ Γ) = ctx-m≤1+nʳ Γ

module _ {Γ : Ctx ω×ω} where
  ▻₂ : Ty (◄₂ Γ) → Ty Γ
  ▻₂ = ⟨ later₂ ∣_⟩

  ▻₂' : Ty Γ → Ty Γ
  ▻₂' T = ▻₂ (T [ from-earlier₂ Γ ])

  next₂ : {T : Ty (◄₂ Γ)} → Tm (◄₂ Γ) T → Tm Γ (▻₂ T)
  next₂ = mod-intro later₂

  prev₂ : {T : Ty (◄₂ Γ)} → Tm Γ (▻₂ T) → Tm (◄₂ Γ) T 
  prev₂ = mod-elim later₂
  
  prev₂' : {T : Ty Γ} → Tm Γ T → Tm (◄₂ Γ) (T [ from-earlier₂ Γ ])
  prev₂' t = t [ from-earlier₂ Γ ]'

  next₂' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻₂' T)
  next₂' t = next₂ (prev₂' t)

  ◄₂-cancel : ◄₂ (𝕪 [ r , suc n ]) ≅ᶜ 𝕪 [ r , n ]
  func (from ◄₂-cancel) [ k≤r , m+1≤n+1 ] = [ k≤r , ≤-pred m+1≤n+1 ]
  naturality (from ◄₂-cancel) = ×-≡,≡→≡ [ refl , ≤-irrelevant _ _ ]
  func (to ◄₂-cancel) [ k≤r , m≤n ] = [ k≤r , s≤s m≤n ]
  naturality (to ◄₂-cancel) = ×-≡,≡→≡ [ refl , ≤-irrelevant _ _ ]
  eq (isoˡ ◄₂-cancel) [ k≤r , m+1≤n+1 ] = ×-≡,≡→≡ [ refl , ≤-irrelevant _ _ ]
  eq (isoʳ ◄₂-cancel) [ k≤r , m≤n ] = ×-≡,≡→≡ [ refl , ≤-irrelevant _ _ ]

  ⇋₂ : {γ : Γ ⟨ [ r , suc n ] ⟩} {T : Ty Γ} → 
      T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ] [ to ◄₂-cancel ] ⟨ [ r , n ] , [ ≤-refl , ≤-refl ] ⟩ →
      Tm (𝕪 [ r , n ]) (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ] [ to ◄₂-cancel ])
  ⇋₂ {γ = γ} {T} t ⟨ _ , [ _ , m≤n ] ⟩' = T ⟪ [ _ , m≤n ] , trans (cong (Γ ⟪ [ _ , m≤n ] ⟫_) (trans (sym (ctx-comp Γ)) (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , ≤-irrelevant _ _ ])))) (trans (ctx-m≤1+nʳ Γ) (cong (Γ ⟪_⟫ (Γ ⟪ [ _ , s≤s m≤n ] ⟫ γ)) (×-≡,≡→≡ [ refl , ≤-irrelevant _ _ ]))) ⟫ t
  naturality (⇋₂ {T = T} _) _ eγ = trans (sym (ty-comp T)) (ty-cong T (×-≡,≡→≡ [ ,-injectiveˡ eγ , ≤-irrelevant _ _ ]))

  ⇋₂⁻¹ : {γ : Γ ⟨ [ r , suc n ] ⟩} {T : Ty Γ} → 
        Tm (𝕪 [ r , n ]) (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ] [ to ◄₂-cancel ]) →
        T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ] [ to ◄₂-cancel ] ⟨ [ r , n ] , [ ≤-refl , ≤-refl ] ⟩
  ⇋₂⁻¹ {r} {n} t = t ⟨ [ r , n ] , [ ≤-refl , ≤-refl ] ⟩'

  null₂ : ∀ {γ} {T : Ty Γ} → Tm (◄₂ (𝕪 [ k , zero ])) (T [ from-earlier₂ Γ ] [ 𝝶-later₂ γ ])
  null₂ ⟨ [ _ , zero ] , () ⟩'
  null₂ ⟨ [ _ , suc n ] , () ⟩'

  löb₂ : (T : Ty Γ) → Tm Γ (▻₂' T ⇛ T) → Tm Γ T
  löb₂ T f = MkTm ((λ { [ r , n ] → tm r n } )) (λ { {[ k , m ]} {[ r , n ]} [ k≤r , m≤n ] eγ → nat k≤r m≤n eγ })
    where
      tm : (r n : Ob ω) → (γ : Γ ⟨ [ r , n ] ⟩) → T ⟨ [ r , n ] , γ ⟩
      tm r zero γ = f €⟨ [ r , zero ] , γ ⟩ null₂
      tm r (suc n) γ = f €⟨ [ r , suc n ] , γ ⟩ 
                      (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ]) _ _) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄₂-cancel) (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ])) (ty-subst-id (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ]))) ]
                      (ιc[ ◄₂-cancel ]' ⇋₂ (tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γ) [ ≤-refl , s≤s ≤-refl ]))))

      open ≡-Reasoning
      nat : {k r m n : Ob ω} {γₙ : Γ ⟨ [ r , n ] ⟩} {γₘ : Γ ⟨ [ k , m ] ⟩} (k≤r : k ≤ r) (m≤n : m ≤ n) (eγ : Γ ⟪ [ k≤r , m≤n ] ⟫ γₙ ≡ γₘ) →
            T ⟪ [ k≤r , m≤n ] , eγ ⟫ tm r n γₙ ≡ tm k m γₘ
      nat {m = zero} {zero} {γₙ} {γₘ} _ z≤n eγ =
        begin
          T ⟪ [ _ , z≤n ] , eγ ⟫
            f €⟨ [ _ , zero ] , γₙ ⟩ null₂
        ≡⟨ €-natural f ⟩
          f €⟨ [ _ , zero ] , γₘ ⟩
            (▻₂' T ⟪ [ _ , z≤n ] , eγ ⟫ null₂)
        ≡⟨ cong (f €⟨ [ _ , zero ] , γₘ ⟩_) (tm-≅-to-≡ (record { eq = λ () })) ⟩
          f €⟨ [ _ , zero ] , γₘ ⟩ null₂ ∎
      nat {m = zero} {suc n} {γₘ = γₘ} _ _ _ = trans (€-natural f) (cong (f €⟨ [ _ , zero ] , γₘ ⟩_) (tm-≅-to-≡ (record { eq = λ () })))
      nat {k} {r} {suc m} {suc n} {γₙ} {γₘ} k≤r (s≤s m≤n) eγ = trans (€-natural f) (cong (f €⟨ [ _ , suc m ] , γₘ ⟩_) (tm-≅-to-≡ iso))
        where
          iso : ▻₂' T ⟪ [ k≤r , s≤s m≤n ] , eγ ⟫
                (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp ((T [ from-earlier₂ Γ ]) [ 𝝶-later₂ γₙ ]) (to ◄₂-cancel) (from ◄₂-cancel)) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄₂-cancel) ((T [ from-earlier₂ Γ ]) [ 𝝶-later₂ γₙ ])) (ty-subst-id ((T [ from-earlier₂ Γ ]) [ 𝝶-later₂ γₙ ]))) ]
                (ιc[ ◄₂-cancel ]' ⇋₂ (tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γₙ) [ ≤-refl , s≤s ≤-refl ]))))
                  ≅ᵗᵐ
                ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp ((T [ from-earlier₂ Γ ]) [ 𝝶-later₂ γₘ ]) (to ◄₂-cancel) (from ◄₂-cancel)) (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄₂-cancel) ((T [ from-earlier₂ Γ ]) [ 𝝶-later₂ γₘ ])) (ty-subst-id ((T [ from-earlier₂ Γ ]) [ 𝝶-later₂ γₘ ]))) ]
                (ιc[ ◄₂-cancel ]' ⇋₂ (tm k m (Γ ⟪ [ ≤-refl , n≤1+n m ] ⟫ func (𝝶-later₂ {Γ} γₘ) [ ≤-refl , s≤s ≤-refl ])))
          eq iso {[ a , b ]} [ a≤k , s≤s b≤m ] =
            begin
              T ⟪ [ ≤-refl , ≤-refl ] , _ ⟫
                T ⟪ [ ≤-refl , ≤-refl ] , _ ⟫
                  T ⟪ [ _ , ≤-pred (≤-trans (s≤s b≤m) (s≤s m≤n)) ] , _ ⟫ 
                    tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γₙ) [ ≤-refl , s≤s ≤-refl ])
            ≡⟨ sym (ty-comp T) ⟩
              T ⟪ [ ≤-trans ≤-refl ≤-refl , ≤-trans ≤-refl ≤-refl ] , _ ⟫
                T ⟪ [ _ , ≤-pred (≤-trans (s≤s b≤m) (s≤s m≤n)) ] , _ ⟫ 
                  tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γₙ) [ ≤-refl , s≤s ≤-refl ])
            ≡⟨ sym (ty-comp T) ⟩
              T ⟪ [ ≤-trans (≤-trans ≤-refl ≤-refl) _ , ≤-trans (≤-trans ≤-refl ≤-refl) (≤-pred (≤-trans (s≤s b≤m) (s≤s m≤n))) ] , _ ⟫
                tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γₙ) [ ≤-refl , s≤s ≤-refl ])
            ≡⟨ ty-cong T (×-≡,≡→≡ [ ≤-irrelevant _ _ , ≤-irrelevant _ _ ]) ⟩
              T ⟪ [ ≤-trans (≤-trans ≤-refl a≤k) k≤r , ≤-trans (≤-trans ≤-refl b≤m) m≤n ] , _ ⟫
                tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γₙ) [ ≤-refl , s≤s ≤-refl ])
            ≡⟨ ty-comp T ⟩
              T ⟪ [ ≤-trans ≤-refl a≤k , ≤-trans ≤-refl b≤m ] , _ ⟫
                T ⟪ [ k≤r , m≤n ] , _ ⟫
                  tm r n (Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ func (𝝶-later₂ {Γ} γₙ) [ ≤-refl , s≤s ≤-refl ])
            ≡⟨ cong (T ⟪ [ ≤-trans ≤-refl a≤k , ≤-trans ≤-refl b≤m ] , _ ⟫_) (nat k≤r m≤n (trans (sym (ctx-comp Γ)) (trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ γₙ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , ≤-irrelevant _ _ ])) (trans (ctx-comp Γ) (trans (ctx-comp Γ) (cong (Γ ⟪ [ ≤-refl , n≤1+n m ] ⟫_ ∘ Γ ⟪ [ ≤-refl , s≤s ≤-refl ] ⟫_) eγ))))))) ⟩
              T ⟪ [ ≤-trans ≤-refl a≤k , ≤-trans ≤-refl b≤m ] , _ ⟫
                tm k m (Γ ⟪ [ ≤-refl , n≤1+n m ] ⟫ func (𝝶-later₂ {Γ} γₘ) [ ≤-refl , s≤s ≤-refl ])
            ≡⟨ ty-comp T ⟩
              T ⟪ [ ≤-refl , ≤-refl ] , _ ⟫
                T ⟪ [ a≤k , b≤m ] , _ ⟫
                  tm k m (Γ ⟪ [ ≤-refl , n≤1+n m ] ⟫ func (𝝶-later₂ {Γ} γₘ) [ ≤-refl , s≤s ≤-refl ]) ∎

  löb₂' : (T : Ty Γ) → Tm (Γ ,, ▻₂' T) (T [ π ]) → Tm Γ T
  löb₂' T f = löb₂ T (lam (▻₂' T) f)

  löb₂[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻₂' T) (T [ π ]) → Tm Γ T
  löb₂[_∈▻'_]_ v = löb₂'

  löb₂-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻₂' T ⇛ T)) → app f (next₂' (löb₂ T f)) ≅ᵗᵐ löb₂ T f
  eq (löb₂-is-fixpoint {T} f) {[ r , zero ]} γ = cong (f €⟨ [ r , zero ] , γ ⟩_) (tm-≅-to-≡ (record { eq = λ () }))
  eq (löb₂-is-fixpoint {T} f) {[ r , suc n ]} γ = cong (f €⟨ [ r , suc n ] , γ ⟩_) (tm-≅-to-≡ iso)
    where
      open ≡-Reasoning
      iso : next₂' (löb₂ T f) ⟨ [ r , suc n ] , γ ⟩'
              ≅ᵗᵐ 
            ι⁻¹[ ≅ᵗʸ-trans (ty-subst-comp (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ]) _ _) 
                (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ ◄₂-cancel) (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ])) 
                           (ty-subst-id (T [ from-earlier₂ Γ ] [ 𝝶-later₂ {Γ} γ ]))) ] 
            (ιc[ ◄₂-cancel ]' ⇋₂ ((löb₂ T f) ⟨ [ r , n ] , Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ (Γ ⟪ [ ≤-refl , s≤s ≤-refl ] ⟫ γ) ⟩'))
      eq iso {[ a , b ]} [ a≤r , s≤s b≤n ] = 
        begin
          (löb₂ T f) ⟨ [ a , b ] , Γ ⟪ [ ≤-refl , n≤1+n b ] ⟫ (Γ ⟪ [ a≤r , s≤s b≤n ] ⟫ γ) ⟩'
        ≡˘⟨ naturality (löb₂ T f) [ ≤-trans ≤-refl a≤r , ≤-trans ≤-refl b≤n ] (trans (sym (trans (ctx-comp Γ) (ctx-comp Γ))) (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , ≤-irrelevant _ _ ])) (ctx-comp Γ))) ⟩
          T ⟪ [ ≤-trans ≤-refl a≤r , ≤-trans ≤-refl b≤n ] , _ ⟫
            (löb₂ T f) ⟨ [ r , n ] , Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ (Γ ⟪ [ ≤-refl , s≤s ≤-refl ] ⟫ γ) ⟩'
        ≡⟨ ty-cong T refl ⟩
          T ⟪ [ ≤-trans ≤-refl a≤r , ≤-trans ≤-refl b≤n ] , _ ⟫
            (löb₂ T f) ⟨ [ r , n ] , Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ (Γ ⟪ [ ≤-refl , s≤s ≤-refl ] ⟫ γ) ⟩'
        ≡⟨ ty-comp T ⟩
          T ⟪ [ ≤-refl , ≤-refl ] , _ ⟫
            T ⟪ [ a≤r , b≤n ] , _ ⟫ 
              (löb₂ T f) ⟨ [ r , n ] , Γ ⟪ [ ≤-refl , n≤1+n n ] ⟫ (Γ ⟪ [ ≤-refl , s≤s ≤-refl ] ⟫ γ) ⟩' ∎

  _⟨$⟩₂_ : {T : Ty (◄₂ Γ)} {S : Ty (◄₂ Γ)} → Tm (◄₂ Γ) (T ⇛ S) → Tm Γ (▻₂ T) → Tm Γ (▻₂ S)
  f ⟨$⟩₂ t = next₂ (app f (prev₂ t))

  _⊛₂_ : {T : Ty (◄₂ Γ)} {S : Ty (◄₂ Γ)} → Tm Γ (▻₂ (T ⇛ S)) → Tm Γ (▻₂ T) → Tm Γ (▻₂ S)
  f ⊛₂ t = prev₂ f ⟨$⟩₂ t

from-earlier-naturalʳ : {Γ Δ : Ctx ω×ω} (σ : Δ ⇒ Γ) → from-earlier₂ Γ ⊚ lock-fmap later₂ σ ≅ˢ σ ⊚ from-earlier₂ Δ
eq (from-earlier-naturalʳ σ) _ = naturality σ

𝟙≤later₂ : TwoCell 𝟙 later₂
transf-op (transf 𝟙≤later₂) = from-earlier₂
CtxNatTransf.naturality (transf 𝟙≤later₂) = from-earlier-naturalʳ

-- This forever modality acts on the left ω of ω×ω only. 
-- todo: FROM HERE
-- decide on whether abstract this.
𝒵×id-flip : Functor ω×ω ω×★
𝒵×id-flip = flip-functor {★} {ω} ∘ᶠ (𝒵 ⊗ᶠ id-functor {ω})

𝒬×id-flip : Functor ω×★ ω×ω
𝒬×id-flip = (𝒬 ⊗ᶠ id-functor {ω}) ∘ᶠ flip-functor {ω} {★}

forever₁ : Modality ω×ω ω×★
forever₁ = fun-to-mod 𝒵×id-flip
-- todo: TILL HERE

-- This forever modality acts on the right ω of ω×ω only. 
id×𝒵 : Functor ω×ω ω×★
id×𝒵 = id-functor {ω} ⊗ᶠ 𝒵 {ω}

forever₂ : Modality ω×ω ω×★
forever₂ = fun-to-mod id×𝒵

constantly-ctx₂ = lock forever₂

id×ω-suc∘id×𝒵=id×𝒵 : id×𝒵 ∘ᶠ id×ω-suc ≅ᶠ id×𝒵
id×ω-suc∘id×𝒵=id×𝒵 = ⊗ᶠ-congˡ id-functor (𝒵∘functor=𝒵 ω-suc)

forever₂-later₂ : forever₂ ⓜ later₂ ≅ᵐ forever₂
forever₂-later₂ = ≅ᵐ-trans (≅ᵐ-sym fun-to-mod-comp) (fun-to-mod-cong id×ω-suc∘id×𝒵=id×𝒵)

forever₂-later₂'-ty : {Γ : Ctx ω×★} (T : Ty (Γ ,lock⟨ forever₂ ⟩)) → ⟨ forever₂ ∣ ▻₂' T ⟩ ≅ᵗʸ ⟨ forever₂ ∣ T ⟩
forever₂-later₂'-ty {Γ = Γ} T =
  begin
    ⟨ forever₂ ∣ ▻₂' T ⟩
  ≅⟨ mod-cong forever₂ (mod-cong later₂ (ty-subst-cong-subst (record { eq = λ _ → refl }) T)) ⟩
    ⟨ forever₂ ∣ ▻₂ (T [ from (eq-lock forever₂-later₂ Γ) ]) ⟩
  ≅⟨ eq-mod-tyˡ forever₂-later₂ T ⟩
    ⟨ forever₂ ∣ T ⟩ ∎
  where open ≅ᵗʸ-Reasoning

-- This constantly modality acts on the right ω of ω×ω only. 
id×𝒬 : Functor ω×★ ω×ω
id×𝒬 = id-functor {ω} ⊗ᶠ 𝒬

constantly₂ : Modality ω×★ ω×ω
constantly₂ = fun-to-mod id×𝒬
 
id×𝒵∘id×𝒬=id : id×𝒵 ∘ᶠ id×𝒬 ≅ᶠ id-functor {ω×★}
id×𝒵∘id×𝒬=id = transᶠ (⊗ᶠ-congˡ id-functor (transᶠ (𝒵∘functor=𝒵 𝒬) 𝒵-id)) ⊗ᶠ-id

forever₂-constantly₂ : forever₂ ⓜ constantly₂ ≅ᵐ 𝟙
forever₂-constantly₂ =
  begin
    forever₂ ⓜ constantly₂
  ≅⟨ ≅ᵐ-sym fun-to-mod-comp ⟩
    fun-to-mod (id×𝒵 ∘ᶠ id×𝒬)
  ≅⟨ fun-to-mod-cong id×𝒵∘id×𝒬=id ⟩
    fun-to-mod id-functor
  ≅⟨ fun-to-mod-id ⟩
    𝟙 ∎
  where open ≅ᵐ-Reasoning

now₂-constantly₂-ctx-intro : {T : ClosedTy ω×★} {{_ : IsClosedNatural T}} {Γ : Ctx ω×★} →
                           Tm Γ T → Tm ((Γ ,lock⟨ forever₂ ⟩) ,lock⟨ constantly₂ ⟩) T
now₂-constantly₂-ctx-intro {T} t = mod-elim constantly₂ (mod-elim forever₂ (ι[ eq-mod-closed forever₂-constantly₂ T ] t))

to-constantly₂-now₂-ctx : (Γ : Ctx ω×ω) → (Γ ⇒ (Γ ,lock⟨ constantly₂ ⟩) ,lock⟨ forever₂ ⟩)
func (to-constantly₂-now₂-ctx Γ) = Γ ⟪ [ ≤-refl , z≤n ] ⟫_
naturality (to-constantly₂-now₂-ctx Γ) {δ = δ} = trans (sym (ctx-comp Γ)) (trans (cong (Γ ⟪_⟫ δ) (×-≡,≡→≡ [ ≤-irrelevant _ _ , ≤-irrelevant _ _ ])) (ctx-comp Γ))

to-constantly₂-now₂-ctx-natural : {Δ Γ : Ctx ω×ω} (σ : Δ ⇒ Γ) →
    to-constantly₂-now₂-ctx Γ ⊚ σ ≅ˢ ctx-fmap (ctx-functor forever₂ ⓕ ctx-functor constantly₂) σ ⊚ to-constantly₂-now₂-ctx Δ
eq (to-constantly₂-now₂-ctx-natural σ) _ = _⇒_.naturality σ

constantly₂∘forever₂≤𝟙 : TwoCell (constantly₂ ⓜ forever₂) 𝟙
transf-op (transf constantly₂∘forever₂≤𝟙) = to-constantly₂-now₂-ctx
CtxNatTransf.naturality (transf constantly₂∘forever₂≤𝟙) = to-constantly₂-now₂-ctx-natural

from-constantly₂-forever₂-ty : {Γ : Ctx ω×ω} {T : Ty ((Γ ,lock⟨ constantly₂ ⟩) ,lock⟨ forever₂ ⟩)} →
                             Tm Γ ⟨ constantly₂ ∣ ⟨ forever₂ ∣ T ⟩ ⟩ → Tm Γ (T [ to-constantly₂-now₂-ctx Γ ])
from-constantly₂-forever₂-ty {Γ = Γ} t = mod-elim forever₂ (mod-elim constantly₂ t) [ to-constantly₂-now₂-ctx Γ ]'





