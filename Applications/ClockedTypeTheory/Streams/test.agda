--------------------------------------------------
-- Definition of semantic guarded streams in base category ω×★
--------------------------------------------------

module Applications.ClockedTypeTheory.Streams.test where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injectiveˡ)
open import Data.Unit using (⊤; tt)
open import Data.Vec hiding ([_]; _⊛_)
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)
open import Level renaming (zero to lzero; suc to lsuc)

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Modality
open import Model.Type.Function
open import Applications.ClockedTypeTheory.Model.Modalities

open BaseCategory

private
  ω×★ : BaseCategory
  ω×★ = ω ⊗ ★

  ★×★ : BaseCategory
  ★×★ = ★ ⊗ ★

  variable
    ℓ ℓ' : Level
    Γ Δ : Ctx ω×★
    m n k r : Ob ω


--------------------------------------------------
-- Some basic operations and proofs regarding vectors
-- Identical to the ones in `module Applications.GuardedRecursion.Model.Streams.Guarded`

first-≤ : {A : Set ℓ} → m ≤ n → Vec A n → Vec A m
first-≤ z≤n as = []
first-≤ (s≤s m≤n) (a ∷ as) = a ∷ first-≤ m≤n as

first-≤-refl : {A : Set ℓ} {as : Vec A n} → first-≤ (≤-refl) as ≡ as
first-≤-refl {as = []}     = refl
first-≤-refl {as = a ∷ as} = cong (a ∷_) first-≤-refl

first-≤-trans : {A : Set ℓ} {k≤m : k ≤ m} {m≤n : m ≤ n} {as : Vec A n} →
                first-≤ (≤-trans k≤m m≤n) as ≡ first-≤ k≤m (first-≤ m≤n as)
first-≤-trans {k≤m = z≤n}                                   = refl
first-≤-trans {k≤m = s≤s k≤m} {m≤n = s≤s m≤n} {as = a ∷ as} = cong (a ∷_) first-≤-trans

map-first-≤ : {A : Set ℓ} {B : Set ℓ'} {f : A → B} {m≤n : m ≤ n} {as : Vec A n} →
              map f (first-≤ m≤n as) ≡ first-≤ m≤n (map f as)
map-first-≤         {m≤n = z≤n}              = refl
map-first-≤ {f = f} {m≤n = s≤s m≤n} {a ∷ as} = cong (f a ∷_) map-first-≤

first-≤-head : {A : Set ℓ} {m≤n : m ≤ n} (as : Vec A (suc n)) →
               head (first-≤ (s≤s m≤n) as) ≡ head as
first-≤-head (a ∷ as) = refl

map-head : {A : Set ℓ} {B : Set ℓ'} {f : A → B} (as : Vec A (suc n)) →
           head (map f as) ≡ f (head as)
map-head (a ∷ as) = refl

first-≤-tail : {A : Set ℓ} {m≤n : m ≤ n} (as : Vec A (suc n)) →
               tail (first-≤ (s≤s m≤n) as) ≡ first-≤ m≤n (tail as)
first-≤-tail (a ∷ as) = refl

map-tail : {A : Set ℓ} {B : Set ℓ'} {f : A → B} (as : Vec A (suc n)) →
           tail (map f as) ≡ map f (tail as)
map-tail (a ∷ as) = refl

map-map-cong : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄} →
               {f : A → B} {g : B → D} {f' : A → C} {g' : C → D} (e : g ∘ f ≗ g' ∘ f') {as : Vec A n} →
               map g (map f as) ≡ map g' (map f' as)
map-map-cong {f = f} {g} {f'} {g'} e {as} =
  begin
    map g (map f as)
  ≡˘⟨ map-∘ g f as ⟩
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map (g' ∘ f') as
  ≡⟨ map-∘ g' f' as ⟩
    map g' (map f' as) ∎
  where open ≡-Reasoning

map-inverse : {A : Set ℓ} {B : Set ℓ'}
              {f : A → B} {g : B → A} (e : g ∘ f ≗ id)
              {as : Vec A n} →
              map g (map f as) ≡ as
map-inverse {f = f} {g} e {as} =
  begin
    map g (map f as)
  ≡˘⟨ map-∘ g f as ⟩
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map id as
  ≡⟨ map-id as ⟩
    as ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Definition of guarded streams in mode ω×★

GStream : Ty (Γ ,lock⟨ constantly₀ ⟩) → Ty Γ
GStream A ⟨ [ n , _ ] , γ ⟩ = Vec (⟨ constantly₀ ∣ A ⟩ ⟨ [ n , _ ] , γ ⟩) (suc n)
GStream A ⟪ [ m≤n , _ ] , eγ ⟫ v = map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ ⟫_) (first-≤ (s≤s m≤n) v)
ty-cong (GStream A) {f = [ m≤n , _ ]} {[ m≤n' , _ ]} e-hom {eγ = eγ} {eγ'} {t = v} = 
  begin
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ ⟫_) (first-≤ (s≤s m≤n) v)
  ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ ⟫_)) (cong (λ x → first-≤ (s≤s x) v) (,-injectiveˡ e-hom)) ⟩
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ ⟫_) (first-≤ (s≤s m≤n') v)
  ≡⟨ map-cong (λ x → ty-cong ⟨ constantly₀ ∣ A ⟩ e-hom {t = x}) _ ⟩
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n' , _ ] , eγ' ⟫_) (first-≤ (s≤s m≤n') v) ∎
  where open ≡-Reasoning
ty-id (GStream A) {t = v} =
  begin
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-refl , _ ] , _ ⟫_) (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-cong (λ x → ty-id ⟨ constantly₀ ∣ A ⟩) _ ⟩
    map id (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-id (first-≤ (s≤s ≤-refl) v) ⟩
    first-≤ (s≤s ≤-refl) v
  ≡⟨ first-≤-refl ⟩
    v ∎
  where open ≡-Reasoning
ty-comp (GStream A) {f = [ k≤m , _ ]} {[ m≤n , _ ]} {eγ-zy = eγ-nm} {eγ-yx = eγ-mk} {t = v} =
  begin
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-trans k≤m m≤n , _ ] , _ ⟫_) (first-≤ (s≤s (≤-trans k≤m m≤n)) v)
  ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-trans k≤m m≤n , _ ] , _ ⟫_)) first-≤-trans ⟩
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-trans k≤m m≤n , _ ] , _ ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-cong (λ x → ty-comp ⟨ constantly₀ ∣ A ⟩ {t = x}) _ ⟩
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ k≤m , _ ] , eγ-mk ⟫_ ∘ ⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ-nm ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-∘ (⟨ constantly₀ ∣ A ⟩ ⟪ [ k≤m , _ ] , eγ-mk ⟫_) (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ-nm ⟫_) _ ⟩
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ k≤m , _ ] , eγ-mk ⟫_) (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ-nm ⟫_)
      (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v)))
  ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ k≤m , _ ] , eγ-mk ⟫_)) map-first-≤ ⟩
    map (⟨ constantly₀ ∣ A ⟩ ⟪ [ k≤m , _ ] , eγ-mk ⟫_) (first-≤ (s≤s k≤m)
      (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ m≤n , _ ] , eγ-nm ⟫_) (first-≤ (s≤s m≤n) v))) ∎
  where open ≡-Reasoning 

module _ {A : Ty (Γ ,lock⟨ constantly₀ ⟩)} where
  g-head : Tm Γ (GStream A ⇛ ⟨ constantly₀ ∣ A ⟩)
  _$⟨_,_⟩_ (g-head ⟨ [ n , _ ] , γn ⟩') _ _ = head -- of the vector
  naturality (g-head ⟨ [ n , _ ] , γn ⟩') {t = v} =
    begin
      head (map (⟨ constantly₀ ∣ A ⟩ ⟪ _ , _ ⟫_) (first-≤ (s≤s _) v))
    ≡⟨ map-head (first-≤ (s≤s _) v) ⟩
      ⟨ constantly₀ ∣ A ⟩ ⟪ _ , _ ⟫ (head (first-≤ (s≤s _) v))
    ≡⟨ cong (⟨ constantly₀ ∣ A ⟩ ⟪ _ , _ ⟫_) (first-≤-head v) ⟩
      ⟨ constantly₀ ∣ A ⟩ ⟪ _ , _ ⟫ head v ∎
    where open ≡-Reasoning
  naturality g-head _ _ = to-pshfun-eq λ _ _ _ → refl

  g-tail : Tm Γ (GStream A ⇛ ▻₀' (GStream A))
  g-tail ⟨ [ n , _ ] , γn ⟩' $⟨ [ z≤n , _ ] , _ ⟩ t = null₀
  {-
    Γ ⊢ g-tail ⟨ [ n , _ ] , γn ⟩' : PshFun (GStream A) (▻₀' (GStream A)) [ n , _ ] γn
    
    NEED: 
      ▻₀ (GStream A [ from-earlier₀ Γ ]) ⟨ [ suc m , _ ] , γ' ⟩
    = Tm (◄ (𝕪 [ suc m , _ ])) ((GStream A) [ from-earlier₀ Γ ] [ 𝝶 ω-suc γ' ])

    WHERE ◄ (𝕪 [ suc m , _ ]) ≅ᶜ 𝕪 [ m , _ ]

    tail t : Vec (⟨ constantly₀ ∣ A ⟩ ⟨ [ suc m , _ ] , γ' ⟩) (suc m)

    1. Tm (𝕪 [ m , _ ]) ((GStream A) [ from-earlier Γ ] [ 𝝶 ω-suc×id {Γ} γ' ] [ to ◄-cancelˡ ]) through ⇋₀ 
    NEED: 
      (GStream A) [ from-earlier Γ ] [ 𝝶 ω-suc×id {Γ} γ' ] [ to ◄-cancelˡ ] ⟨ [ m , _ ] , [ ≤-refl , hom-id V ] ⟩
      = Vec (⟨ constantly₀ ∣ A ⟩ ⟨ [ m , _ ] , func func func γ ⟩) (suc m)
      map () (tail t)
    2. Tm (◄ (𝕪 [ suc m , _ ])) ((GStream A) [ from-earlier₀ Γ ] [ 𝝶 ω-suc γ' ] [ to ◄-cancelˡ ] [ from ◄-cancelˡ ])
    3. Tm (◄ (𝕪 [ suc m , _ ])) ((GStream A) [ from-earlier₀ Γ ] [ 𝝶 ω-suc γ' ]) through type equivalence
    
    ⟨ constantly₀ ∣ A ⟩ ⟨ [ suc m , _ ] , γ' ⟩ = 
    Tm (◄ (𝕪 [ suc m , _ ])) (A [ 𝝶 Q×id γ' ])
  -}
  _$⟨_,_⟩_ (g-tail ⟨ [ n , _ ] , γn ⟩') {y = [ suc m , _ ]} [ s≤s m≤n , _ ] {γ'} _ t = ι⁻¹[ iso ] tm'
    where
      tm : Tm (𝕪 [ m , _ ]) ((GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ] [ to (◄₀-cancel {Γ}) ])
      tm = ⇋₀ (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ n≤1+n m , _ ] , trans (cong (Γ ⟪_⟫ γ')  (×-≡,≡→≡ [ ≤-irrelevant _ _ , refl ])) (ctx-comp Γ) ⟫_) (tail t))

      tm' : Tm (◄₀ (𝕪 [ suc m , _ ])) ((GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ] [ to (◄₀-cancel {Γ}) ] [ from (◄₀-cancel {Γ}) ])
      tm' = ιc[ ◄₀-cancel {Γ} ]' tm

      open ≅ᵗʸ-Reasoning
      iso : (GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ] [ to (◄₀-cancel {Γ}) ] [ from (◄₀-cancel {Γ}) ]
              ≅ᵗʸ
            (GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ]
      iso = ≅ᵗʸ-trans (ty-subst-comp ((GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ]) _ _) 
           (≅ᵗʸ-trans (ty-subst-cong-subst (isoˡ (◄₀-cancel {Γ})) ((GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ])) 
                      (ty-subst-id ((GStream A) [ from-earlier₀ Γ ] [ 𝝶-later₀ {Γ} γ' ])))
  naturality (g-tail ⟨ [ n , _ ] , γn ⟩') {[ zero , _ ]} {[ m , _ ]} {ρ-xy = [ z≤n , _ ]} {ρ-yz = [ m≤n , _ ]} {eγ-zy = eγ-zy} {eγ-yx} {t} = tm-≅-to-≡ (record { eq = λ () })
  naturality (g-tail ⟨ [ n , _ ] , γn ⟩') {[ suc k , _ ]} {[ suc m , _ ]} {ρ-xy = [ s≤s k≤m , _ ]} {ρ-yz = [ m+1≤n , _ ]} {eγ-zy = eγ-zy} {eγ-yx} {t} = tm-≅-to-≡ {!   !} 
    where
      iso : g-tail ⟨ [ n , _ ] , γn ⟩' $⟨ [ ≤-trans (s≤s k≤m) (m+1≤n) , _ ] , strong-ctx-comp Γ eγ-zy eγ-yx ⟩
            (GStream A ⟪ [ s≤s k≤m , _ ] , eγ-yx ⟫ t)
              ≅ᵗᵐ
            ▻₀' (GStream A) ⟪ [ s≤s k≤m , _ ] , eγ-yx ⟫
            g-tail ⟨ [ n , _ ] , γn ⟩' $⟨ [ m+1≤n , _ ] , eγ-zy ⟩ t
      eq iso {[ j , _ ]} [ s≤s j≤k , _ ] =
        begin
          (g-tail ⟨ [ n , _ ] , γn ⟩' $⟨ [ ≤-trans (s≤s k≤m) m+1≤n , _ ] , strong-ctx-comp Γ eγ-zy eγ-yx ⟩
          (GStream A ⟪ [ s≤s k≤m , _ ] , eγ-yx ⟫ t))
          ⟨ [ j , _ ] , [ s≤s j≤k , _ ] ⟩'
        ≡⟨ {!   !} ⟩
          map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-refl , _ ] , _ ⟫_) 
          ((g-tail ⟨ [ n , _ ] , γn ⟩' $⟨ [ m+1≤n , _ ] , eγ-zy ⟩ t) ⟨ [ j , _ ] , [ ≤-trans (s≤s j≤k) (s≤s k≤m) , _ ] ⟩')
        ≡˘⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-refl , _ ] , _ ⟫_)) first-≤-refl ⟩
          map (⟨ constantly₀ ∣ A ⟩ ⟪ [ ≤-refl , _ ] , _ ⟫_) (first-≤ (s≤s ≤-refl) ((g-tail ⟨ [ n , _ ] , γn ⟩' $⟨ [ m+1≤n , _ ] , eγ-zy ⟩ t) ⟨ [ j , _ ] , [ ≤-trans (s≤s j≤k) (s≤s k≤m) , _ ] ⟩')) ∎
        where open ≡-Reasoning
    -- begin
    --   map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_) (tail (map (⟨ constantly₀ ∣ A ⟩ ⟪ s≤s k≤m , _ ⟫_) (first-≤ (s≤s (s≤s k≤m)) v)))
    -- ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_)) (map-tail (first-≤ (s≤s (s≤s k≤m)) v)) ⟩
    --   map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_) (map (⟨ constantly₀ ∣ A ⟩ ⟪ s≤s k≤m , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    -- ≡⟨ map-map-cong (λ _ → ty-cong-2-2 (⟨ constantly₀ ∣ A ⟩) (≤-irrelevant _ _)) ⟩
    --   map (⟨ constantly₀ ∣ A ⟩ ⟪ k≤m , _ ⟫_) (map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    -- ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ k≤m , _ ⟫_) ∘ map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_)) (first-≤-tail v) ⟩
    --   map (⟨ constantly₀ ∣ A ⟩ ⟪ k≤m , _ ⟫_) (map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_) (first-≤ (s≤s k≤m) (tail v)))
    -- ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ k≤m , _ ⟫_)) map-first-≤ ⟩
    --   map (⟨ constantly₀ ∣ A ⟩ ⟪ k≤m , _ ⟫_) (first-≤ (s≤s k≤m) (map (⟨ constantly₀ ∣ A ⟩ ⟪ n≤1+n _ , _ ⟫_) (tail v))) ∎
    -- where open ≡-Reasoning
  naturality g-tail [ z≤n , _ ]       eγ = {!   !} -- to-pshfun-eq λ { z≤n _ _ → refl }
  naturality g-tail [ s≤s m≤n , _ ] eγ = {!   !} -- to-pshfun-eq λ { z≤n _ _ → refl ; (s≤s k≤m) _ _ → refl }

  -- prim-g-cons : Tm (Γ ,, ⟨ constantly₀ ∣ A ⟩ ,, (▻' (GStream A)) [ π ]) (((GStream A) [ π ]) [ π ])
  -- prim-g-cons ⟨ zero ,    [ [ γn , a ] , t ] ⟩' = a ∷ []
  -- prim-g-cons ⟨ (suc n) , [ [ γn , a ] , t ] ⟩' = a ∷ map (ty-ctx-subst A (sym (ctx-comp Γ))) t
  -- naturality prim-g-cons {y = zero}  z≤n       refl = refl
  -- naturality prim-g-cons {y = suc n} z≤n       refl = refl
  -- naturality prim-g-cons             (s≤s m≤n) refl = cong (⟨ constantly₀ ∣ A ⟩ ⟪ s≤s m≤n , refl ⟫ _ ∷_) (sym (
  --   begin
  --     map (ty-ctx-subst A _) (map (⟨ constantly₀ ∣ A ⟩ ⟪ m≤n , _ ⟫_) (first-≤ (s≤s m≤n) _))
  --   ≡⟨ map-map-cong (λ _ → ty-cong-2-2 A refl) ⟩
  --     map (⟨ constantly₀ ∣ A ⟩ ⟪ s≤s m≤n , refl ⟫_) (map (ty-ctx-subst A _) (first-≤ (s≤s m≤n) _))
  --   ≡⟨ cong (map (⟨ constantly₀ ∣ A ⟩ ⟪ s≤s m≤n , refl ⟫_)) map-first-≤ ⟩
  --     map (⟨ constantly₀ ∣ A ⟩ ⟪ s≤s m≤n , refl ⟫_) (first-≤ (s≤s m≤n) (map (ty-ctx-subst A _) _)) ∎))
  --   where open ≡-Reasoning

  -- g-cons : Tm Γ (⟨ constantly₀ ∣ A ⟩ ⇛ ▻' (GStream A) ⇛ GStream A)
  -- g-cons = lam (⟨ constantly₀ ∣ A ⟩) (ι[ ⇛-natural π ]
  --              lam (▻' (GStream A) [ π ])
  --                  prim-g-cons) 