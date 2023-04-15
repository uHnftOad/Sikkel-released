--------------------------------------------------
-- Contexts and substitutions + category structure
--------------------------------------------------

module Model.CwF-Structure.Context where

open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to [_,_])

open import Model.BaseCategory
open import Model.Helpers

--------------------------------------------------
-- Definition of contexts and substitutions as presheaves over C

record Ctx (C : BaseCategory) : Set₁ where
  constructor MkCtx
  no-eta-equality

  open BaseCategory C

  field
    ctx-cell : Ob → Set
    ctx-hom : ∀ {x y} → Hom x y → ctx-cell y → ctx-cell x
    ctx-id : ∀ {x} {γ : ctx-cell x} → ctx-hom hom-id γ ≡ γ
      {-
        Γ ⟪ hom-id C {x} ⟫ : Γ ⟨ x ⟩ → Γ ⟨ x ⟩    
        γ : Γ ⟨ x ⟩ 
        ---------------------------------------
        Γ ⟪ hom-id C {x} ⟫ γ = γ
      -}
    ctx-comp : ∀ {x y z} {f : Hom x y} {g : Hom y z} {γ : ctx-cell z} →
               ctx-hom (g ∙ f) γ ≡ ctx-hom f (ctx-hom g γ)
      {-
                  Γ ⟪ f ⟫_           Γ ⟪ g ⟫_
        Γ ⟨ x ⟩ ←--------- Γ ⟨ y ⟩ ←--------- Γ ⟨ z ⟩ ∋ γ 
        Γ ⟨ x ⟩ ←----------------------------- Γ ⟨ z ⟩ ∋ γ
                          Γ ⟪ g ∙ f ⟫_
      -}
open Ctx public renaming (ctx-cell to _⟨_⟩; ctx-hom to _⟪_⟫_)

module _ {C : BaseCategory} where
  infix 10 _⇒_
  infix 1 _≅ˢ_
  infixl 20 _⊚_

  open BaseCategory C

  private
    variable
      x y z : Ob
      Δ Γ Θ : Ctx C

  -- The following proof is needed to define composition of morphisms in the category of elements
  -- of Γ and is used e.g. in the definition of types (in CwF-Structure.Types) and the definition
  -- of function types.
  strong-ctx-comp : (Γ : Ctx C) {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
                    (eq-zy : Γ ⟪ g ⟫ γz ≡ γy) (eq-yx : Γ ⟪ f ⟫ γy ≡ γx) →
                    Γ ⟪ g ∙ f ⟫ γz ≡ γx
  strong-ctx-comp Γ {f}{g}{γz}{γy}{γx} eq-zy eq-yx =
    begin
      Γ ⟪ g ∙ f ⟫ γz
    ≡⟨ ctx-comp Γ ⟩
      Γ ⟪ f ⟫ (Γ ⟪ g ⟫ γz)
    ≡⟨ cong (Γ ⟪ f ⟫_) eq-zy ⟩
      Γ ⟪ f ⟫ γy
    ≡⟨ eq-yx ⟩
      γx ∎
    where open ≡-Reasoning

  -- The type of substitutions from context Δ to context Γ
  record _⇒_ (Δ : Ctx C) (Γ : Ctx C) : Set where
    constructor MkSubst
    no-eta-equality
    field
      func : ∀ {x} → Δ ⟨ x ⟩ → Γ ⟨ x ⟩
      naturality : ∀ {x y} {f : Hom x y} {δ : Δ ⟨ y ⟩} → Γ ⟪ f ⟫ (func δ) ≡ func (Δ ⟪ f ⟫ δ)
        {-
                              f
                    x -----------------→ y

          (2)            Δ ⟪ f ⟫_
               Δ ⟨ x ⟩ ←----------- Δ ⟨ y ⟩ ∋ δ
                   ∣                    ∣
          func {x} ∣                    ∣ func {y}
                   ↓                    ↓
               Γ ⟨ x ⟩ ←----------- Γ ⟨ y ⟩
                          Γ ⟪ f ⟫_            (1)
        -}
  open _⇒_ public

  id-subst : (Γ : Ctx C) → Γ ⇒ Γ
  func (id-subst Γ) = id
  naturality (id-subst Γ) = refl

  -- Composition of substitutions
  _⊚_ : Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
  func (τ ⊚ σ) = func τ ∘ func σ
  naturality (_⊚_ {Γ = Γ}{Θ = Θ}{Δ = Δ} τ σ) {f = f} {δ = δ} =
    begin
      Θ ⟪ f ⟫ (func τ (func σ δ))
    ≡⟨ naturality τ ⟩
      func τ (Γ ⟪ f ⟫ func σ δ)
    ≡⟨ cong (func τ) (naturality σ) ⟩
      func τ (func σ (Δ ⟪ f ⟫ δ)) ∎
    where open ≡-Reasoning


  --------------------------------------------------
  -- Equivalence of substitutions

  -- Two substitutions σ, τ : Δ ⇒ Γ are equivalent if they map every value of
  -- Δ ⟨ x ⟩ (for any object x) to propositionally equal values of Γ ⟨ x ⟩.
  record _≅ˢ_ {Δ : Ctx C} {Γ : Ctx C} (σ τ : Δ ⇒ Γ) : Set where
    field
      eq : ∀ {x} δ → func σ {x} δ ≡ func τ δ
        -- δ : Δ ⟨ x ⟩
  open _≅ˢ_ public

  -- Properties of equivalence of substitutions
  ≅ˢ-refl : {σ : Δ ⇒ Γ} → σ ≅ˢ σ
  eq ≅ˢ-refl _ = refl

  ≅ˢ-sym : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → τ ≅ˢ σ
  eq (≅ˢ-sym σ=τ) δ = sym (eq σ=τ δ)

  ≅ˢ-trans : {σ τ ψ : Δ ⇒ Γ} → σ ≅ˢ τ → τ ≅ˢ ψ → σ ≅ˢ ψ
  eq (≅ˢ-trans σ=τ τ=ψ) δ = trans (eq σ=τ δ) (eq τ=ψ δ)

  module ≅ˢ-Reasoning where
    infix  3 _∎
    infixr 2 _≅⟨⟩_ step-≅ step-≅˘
    infix  1 begin_

    begin_ : ∀ {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → σ ≅ˢ τ
    begin_ σ=τ = σ=τ

    _≅⟨⟩_ : ∀ (σ {τ} : Δ ⇒ Γ) → σ ≅ˢ τ → σ ≅ˢ τ
    _ ≅⟨⟩ σ=τ = σ=τ

    step-≅ : ∀ (σ {τ ψ} : Δ ⇒ Γ) → τ ≅ˢ ψ → σ ≅ˢ τ → σ ≅ˢ ψ
    step-≅ _ τ≅ψ σ≅τ = ≅ˢ-trans σ≅τ τ≅ψ

    step-≅˘ : ∀ (σ {τ ψ} : Δ ⇒ Γ) → τ ≅ˢ ψ → τ ≅ˢ σ → σ ≅ˢ ψ
    step-≅˘ _ τ≅ψ τ≅σ = ≅ˢ-trans (≅ˢ-sym τ≅σ) τ≅ψ

    _∎ : ∀ (σ : Δ ⇒ Γ) → σ ≅ˢ σ
    _∎ _ = ≅ˢ-refl

    syntax step-≅  σ τ≅ψ σ≅τ = σ ≅⟨  σ≅τ ⟩ τ≅ψ
    syntax step-≅˘ σ τ≅ψ τ≅σ = σ ≅˘⟨ τ≅σ ⟩ τ≅ψ


  --------------------------------------------------
  -- Laws for the category of contexts

  ⊚-id-substʳ : (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≅ˢ σ
  eq (⊚-id-substʳ σ) _ = refl

  ⊚-id-substˡ : (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≅ˢ σ
  eq (⊚-id-substˡ σ) _ = refl

  ⊚-assoc : {Γ₁ : Ctx C} {Γ₂ : Ctx C} {Γ₃ : Ctx C} {Γ₄ : Ctx C}
             {σ₃₄ : Γ₃ ⇒ Γ₄} {σ₂₃ : Γ₂ ⇒ Γ₃} {σ₁₂ : Γ₁ ⇒ Γ₂} →
             (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≅ˢ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
  eq ⊚-assoc _ = refl

  ⊚-congˡ : {τ : Γ ⇒ Θ} {σ σ' : Δ ⇒ Γ} → σ ≅ˢ σ' → τ ⊚ σ ≅ˢ τ ⊚ σ'
  eq (⊚-congˡ {τ = τ} σ=σ') δ = cong (func τ) (eq σ=σ' δ)

  ⊚-congʳ : {τ τ' : Γ ⇒ Θ} {σ : Δ ⇒ Γ} → τ ≅ˢ τ' → τ ⊚ σ ≅ˢ τ' ⊚ σ
  eq (⊚-congʳ {σ = σ} τ=τ') δ = eq τ=τ' (func σ δ)


  --------------------------------------------------
  -- The empty context (i.e. terminal object in the category of contexts)

  ◇ : Ctx C
  ◇ ⟨ _ ⟩ = ⊤
  ◇ ⟪ _ ⟫ _ = tt
  ctx-id ◇ = refl
  ctx-comp ◇ = refl

  !◇ : (Γ : Ctx C) → Γ ⇒ ◇
  func (!◇ Γ) _ = tt
  naturality (!◇ Γ) = refl

  -- A proof that ◇ is indeed terminal
  ◇-terminal : (Γ : Ctx C) (σ τ : Γ ⇒ ◇) → σ ≅ˢ τ
  eq (◇-terminal Γ σ τ) _ = refl

--------------------------------------------------
-- Functions related to contexts over a product base category C ⊗ D

-- Fix an object c in C and take the projection of a context over C ⊗ D along with c
fixˡ : ∀ {C D} → Ctx (C ⊗ D) → BaseCategory.Ob C → Ctx D
fixˡ Γ c ⟨ d ⟩ = Γ ⟨ [ c , d ] ⟩
fixˡ {C = C} Γ c ⟪ g ⟫ γ = Γ ⟪ [ BaseCategory.hom-id C {c} , g ] ⟫ γ
ctx-id (fixˡ Γ c) = ctx-id Γ
ctx-comp (fixˡ {C = C} Γ c) {γ = γ} = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ sym (BaseCategory.hom-idˡ C) , refl ])) (ctx-comp Γ)


-- Fix an object d in D and take the projection of a context over C ⊗ D along with d
fixʳ : ∀ {C D} → Ctx (C ⊗ D) → BaseCategory.Ob D → Ctx C
fixʳ Γ d ⟨ c ⟩ = Γ ⟨ [ c , d ] ⟩
fixʳ {D = D} Γ d ⟪ f ⟫ γ = Γ ⟪ [ f , BaseCategory.hom-id D {d} ] ⟫ γ
ctx-id (fixʳ Γ d) = ctx-id Γ
ctx-comp (fixʳ {D = D} Γ d) {γ = γ} = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (BaseCategory.hom-idˡ D) ])) (ctx-comp Γ)

-- Alternative syntax of fixʳ and fixˡ
-- `ˡ` and `ʳ` indicate which of the left and right categories is being fixed
_⟨_⟩ˡ : ∀ {C D} → Ctx (C ⊗ D) → BaseCategory.Ob C  → Ctx D
Γ ⟨ c ⟩ˡ = fixˡ Γ c

_⟨_⟩ʳ : ∀ {C D} → Ctx (C ⊗ D) → BaseCategory.Ob D → Ctx C
Γ ⟨ d ⟩ʳ = fixʳ Γ d

-- Given a morphism f : c₁ → c₂ in C, construct a subsitution from Γ ⟨ c₂ ⟩ˡ to Γ ⟨ c₁ ⟩ˡ
const-substˡ : ∀ {C D} {c₁ c₂ : BaseCategory.Ob C} → 
  (Γ : Ctx (C ⊗ D)) → 
  (BaseCategory.Hom C c₁ c₂) → 
  Γ ⟨ c₂ ⟩ˡ ⇒ Γ ⟨ c₁ ⟩ˡ
func (const-substˡ {D = D} Γ f) = Γ ⟪ [ f , BaseCategory.hom-id D ] ⟫_
naturality (const-substˡ {C} {D} Γ f) {f = g} {δ = δ} = trans (sym (ctx-comp Γ))
                                                        (trans (cong (Γ ⟪_⟫ δ) (×-≡,≡→≡ [ BaseCategory.hom-idⁱ C , BaseCategory.hom-idᵒ D ]))
                                                               (ctx-comp Γ))

-- Given a morphism g : d₁ → d₂ in D, construct a subsitution from Γ ⟨ d₂ ⟩ʳ to Γ ⟨ d₁ ⟩ʳ
const-substʳ : ∀ {C D} {d₁ d₂ : BaseCategory.Ob D} → (Γ : Ctx (C ⊗ D)) → (BaseCategory.Hom D d₁ d₂) → Γ ⟨ d₂ ⟩ʳ ⇒ Γ ⟨ d₁ ⟩ʳ
func (const-substʳ {C = C} Γ g) = Γ ⟪ [ BaseCategory.hom-id C , g ] ⟫_
naturality (const-substʳ {C} {D} Γ g) {f = f} {δ = δ} = trans (sym (ctx-comp Γ))
                                                        (trans (cong (Γ ⟪_⟫ δ) (×-≡,≡→≡ [ BaseCategory.hom-idᵒ C , BaseCategory.hom-idⁱ D ]))
                                                               (ctx-comp Γ))

-- const-substˡ Γ (hom-id C {c}) ≅ˢ id-subst (Γ ⟨ c ⟩ˡ)
≅ˢ-const-substˡ : ∀ {C D} {c : BaseCategory.Ob C} → (Γ : Ctx (C ⊗ D)) → 
  const-substˡ Γ (BaseCategory.hom-id C) ≅ˢ id-subst (Γ ⟨ c ⟩ˡ)
eq (≅ˢ-const-substˡ Γ) γ = ctx-id Γ

-- const-substʳ Γ (hom-id D {d}) ≅ˢ id-subst (Γ ⟨ d ⟩ʳ)
≅ˢ-const-substʳ : ∀ {C D} {d : BaseCategory.Ob D} → (Γ : Ctx (C ⊗ D)) → 
  const-substʳ Γ (BaseCategory.hom-id D) ≅ˢ id-subst (Γ ⟨ d ⟩ʳ)
eq (≅ˢ-const-substʳ Γ) γ = ctx-id Γ

⊚-comp-const-substˡ : ∀ {C D} {c₁ c₂ c₃ : BaseCategory.Ob C} → 
  (Γ : Ctx (C ⊗ D)) → 
  (f₁ : BaseCategory.Hom C c₁ c₂) → 
  (f₂ : BaseCategory.Hom C c₂ c₃) → 
  const-substˡ Γ (BaseCategory._∙_ C f₂ f₁) ≅ˢ const-substˡ Γ f₁ ⊚ const-substˡ Γ f₂
eq (⊚-comp-const-substˡ {D = D} Γ f₁ f₂) γ = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (BaseCategory.hom-idˡ D) ])) (ctx-comp Γ)
{-
  -- : func const-substˡ Γ (BaseCategory._∙_ C f₂ f₁) γ ≡ func (const-substˡ Γ f₁ ⊚ const-substˡ Γ f₂) γ
  -- = Γ ⟪ [ BaseCategory._∙_ C f₂ f₁ , BaseCategory.hom-id D ] ⟫ γ ≡ Γ ⟪ [ f₁ , BaseCategory.hom-id D ] ⟫ (Γ ⟪ [ f₂ , BaseCategory.hom-id D ] ⟫ γ)

    Γ ⟪ [ BaseCategory._∙_ C f₂ f₁ , hom-id D ] ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (BaseCategory.hom-idˡ D) ]) ⟩
    Γ ⟪ [ BaseCategory._∙_ C f₂ f₁ , hom-id D ∙ hom-id D ] ⟫ γ
  ≡⟨⟩
    Γ ⟪ [ f₂ , hom-id D ] ∙ [ f₁ , hom-id D ] ⟫ γ
  ≡⟨ ctx-comp Γ ⟩
    Γ ⟪ [ f₁ , hom-id D ] ⟫ (Γ ⟪ [ f₂ , hom-id D ] ⟫ γ)
  ≡⟨⟩
    func (const-substˡ Γ f₁) (func (const-substˡ Γ f₂) γ)
  ≡⟨⟩
    func (const-substˡ Γ f₁ ⊚ const-substˡ Γ f₂) γ
    cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ BaseCategory.hom-idᵒ C , BaseCategory.hom-idᵒ D ])
-}

⊚-comp-const-substʳ : ∀ {C D} {d₁ d₂ d₃ : BaseCategory.Ob D} → 
  (Γ : Ctx (C ⊗ D)) → 
  (g₁ : BaseCategory.Hom D d₁ d₂) → 
  (g₂ : BaseCategory.Hom D d₂ d₃) → 
  const-substʳ Γ (BaseCategory._∙_ D g₂ g₁) ≅ˢ const-substʳ Γ g₁ ⊚ const-substʳ Γ g₂
eq (⊚-comp-const-substʳ {C = C} Γ g₁ g₂) γ = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ sym (BaseCategory.hom-idˡ C) , refl ])) (ctx-comp Γ)

-- Given a substitution between contexts in C×D, fix an object c in C, and construct a subsitution in D
fix-substˡ : ∀ {C D} {Δ Γ : Ctx (C ⊗ D)} → (σ : Δ ⇒ Γ) → (c : BaseCategory.Ob C) → Δ ⟨ c ⟩ˡ ⇒ Γ ⟨ c ⟩ˡ
func (fix-substˡ σ c) {d} = func σ {[ c , d ]}
naturality (fix-substˡ σ c) = naturality σ

-- Given a substitution between contexts in C×D, fix an object d in D, and construct a subsitution in C
fix-substʳ : ∀ {C D} {Δ Γ : Ctx (C ⊗ D)} → (σ : Δ ⇒ Γ) → (d : BaseCategory.Ob D) → Δ ⟨ d ⟩ʳ ⇒ Γ ⟨ d ⟩ʳ
func (fix-substʳ σ d) {c} = func σ {[ c , d ]}
naturality (fix-substʳ σ c) = naturality σ

-- The two substitution constructors `fix-substˡ` and `const-substˡ` commute.
fix-const-substˡ : ∀ {C D} {c₁ c₂ : BaseCategory.Ob C} {Δ Γ : Ctx (C ⊗ D)} {f : BaseCategory.Hom C c₁ c₂} {σ : Δ ⇒ Γ} → 
  (const-substˡ Γ f) ⊚ (fix-substˡ σ c₂) ≅ˢ (fix-substˡ σ c₁) ⊚ (const-substˡ Δ f)
eq (fix-const-substˡ {σ = σ}) γ = naturality σ
{-
  RHS:
    func ((const-substˡ Γ f) ⊚ (fix-substˡ σ c₂)) {d} γ ≡ func ((fix-substˡ σ c₁) ⊚ (const-substˡ Δ f)) {d} γ
    func ((const-substˡ Γ f) ⊚ (fix-substˡ σ c₂)) {d} γ
  ≡⟨⟩
    func (const-substˡ Γ f) {d} (func (fix-substˡ σ c₂) {d} γ)
  ≡⟨⟩
    func (const-substˡ Γ f) (func σ {[ c₂ , d ]} γ)
  ≡⟨ naturality σ ⟩
    Γ ⟪ [ f , BaseCategory.hom-id D ] ⟫ (func σ {[ c₂ , d ]} γ)


  ≡⟨⟩
    func σ {[ c₁ , d ]} (Δ ⟪ [ f , BaseCategory.hom-id D ] ⟫ γ)
  ≡⟨⟩
    func (fix-substˡ σ c₁) (func (const-substˡ Δ f) γ)
  ≡⟨⟩
    func ((fix-substˡ σ c₁) ⊚ (const-substˡ Δ f)) {d} γ

-}

-- The two substitution constructors `fix-substʳ` and `const-substʳ` commute.
fix-const-substʳ : ∀ {C D} {d₁ d₂ : BaseCategory.Ob D} {Δ Γ : Ctx (C ⊗ D)} {g : BaseCategory.Hom D d₁ d₂} {σ : Δ ⇒ Γ} → 
  (const-substʳ Γ g) ⊚ (fix-substʳ σ d₂) ≅ˢ (fix-substʳ σ d₁) ⊚ (const-substʳ Δ g)
eq (fix-const-substʳ {σ = σ}) γ = naturality σ

-- `fix-substˡ` respects equivalence of substitutions.
fix-substˡ-cong : ∀ {C D} {Δ Γ : Ctx (C ⊗ D)} {σ τ : Δ ⇒ Γ} {c : BaseCategory.Ob C} → 
  σ ≅ˢ τ → fix-substˡ σ c ≅ˢ fix-substˡ τ c
eq (fix-substˡ-cong σ=τ) = eq σ=τ

-- `fix-substʳ` respects equivalence of substitutions.
fix-substʳ-cong : ∀ {C D} {Δ Γ : Ctx (C ⊗ D)} {σ τ : Δ ⇒ Γ} {d : BaseCategory.Ob D} → 
  σ ≅ˢ τ → fix-substʳ σ d ≅ˢ fix-substʳ τ d
eq (fix-substʳ-cong σ=τ) = eq σ=τ

-- `fix-substˡ` preserves identity subsitutions.
fix-substˡ-id : ∀ {C D} {Γ : Ctx (C ⊗ D)} {c : BaseCategory.Ob C} → 
  fix-substˡ (id-subst Γ) c ≅ˢ id-subst (Γ ⟨ c ⟩ˡ)
eq fix-substˡ-id γ = refl

-- `fix-substʳ` preserves identity subsitutions.
fix-substʳ-id : ∀ {C D} {Γ : Ctx (C ⊗ D)} {d : BaseCategory.Ob D} → 
  fix-substʳ (id-subst Γ) d ≅ˢ id-subst (Γ ⟨ d ⟩ʳ)
eq fix-substʳ-id γ = refl

-- `fix-substˡ` commutes with composition of substitutions.
fix-substˡ-⊚ : ∀ {C D} {Δ Γ Θ : Ctx (C ⊗ D)} {c : BaseCategory.Ob C} → 
  (τ : Γ ⇒ Θ) → (σ : Δ ⇒ Γ) → 
  fix-substˡ (τ ⊚ σ) c ≅ˢ fix-substˡ τ c ⊚ fix-substˡ σ c
eq (fix-substˡ-⊚ τ σ) γ = refl

-- `fix-substʳ` commutes with composition of substitutions.
fix-substʳ-⊚ : ∀ {C D} {Δ Γ Θ : Ctx (C ⊗ D)} {d : BaseCategory.Ob D} → 
  (τ : Γ ⇒ Θ) → (σ : Δ ⇒ Γ) → 
  fix-substʳ (τ ⊚ σ) d ≅ˢ fix-substʳ τ d ⊚ fix-substʳ σ d
eq (fix-substʳ-⊚ τ σ) γ = refl