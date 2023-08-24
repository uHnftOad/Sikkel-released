--------------------------------------------------
-- Definition of the different expressions occurring
-- in the mode theory for guarded recursion
--------------------------------------------------

module Applications.ClockedTypeTheory.MSTT.ModeTheory where

open import Data.String

open import Model.BaseCategory as M hiding (★; ω)
open import Model.Functor as M
open import Model.CwF-Structure as M
open import Model.Modality as M hiding (𝟙; _ⓜ_; _ⓣ-vert_; _ⓣ-hor_)
open import Applications.ClockedTypeTheory.Model.★⇆ω as M hiding
  (constantly; forever; later; 𝟙≤later)
  -- (constantly; forever; later; 𝟙≤later; constantly∘forever≤𝟙)
open import Applications.ClockedTypeTheory.Model.ω⇆ω×ω as M hiding 
  (𝒍𝒂𝒕𝒆𝒓₁; 𝒍𝒂𝒕𝒆𝒓₂; 𝒇𝒐𝒓𝒆𝒗𝒆𝒓; 𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚; ω×★; ω×ω; ★×ω; ★×★)


--------------------------------------------------
-- Expressions representing modes, modalities and 2-cells

data ModeExpr : Set where
  ★ ω ω×ω : ModeExpr

private
  variable
    m m₁ m₂ m₃  : ModeExpr

infixl 5 _ⓜ_
data ModalityExpr : ModeExpr → ModeExpr → Set where
  𝟙 : ModalityExpr m m
  _ⓜ_ : ModalityExpr m₂ m₃  → ModalityExpr m₁ m₂ → ModalityExpr m₁ m₃ 
  constantly : ModalityExpr ★ ω
  forever : ModalityExpr ω ★
  later : ModalityExpr ω ω
  𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₁ : ModalityExpr ω ω×ω
  𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₂ : ModalityExpr ω ω×ω
  𝒇𝒐𝒓𝒆𝒗𝒆𝒓₁ : ModalityExpr ω×ω ω
  𝒇𝒐𝒓𝒆𝒗𝒆𝒓₂ : ModalityExpr ω×ω ω
  𝒍𝒂𝒕𝒆𝒓₁ : ModalityExpr ω×ω ω×ω
  𝒍𝒂𝒕𝒆𝒓₂ : ModalityExpr ω×ω ω×ω


infixl 5 _ⓣ-hor_
infixl 6 _ⓣ-vert_
data TwoCellExpr : Set where
  id-cell : TwoCellExpr
  _ⓣ-vert_ : TwoCellExpr → TwoCellExpr → TwoCellExpr
  _ⓣ-hor_ : TwoCellExpr → TwoCellExpr → TwoCellExpr
  𝟙≤later : TwoCellExpr
  constantly∘forever≤𝟙 : TwoCellExpr
  𝟙≤𝒍𝒂𝒕𝒆𝒓₁ : TwoCellExpr
  𝟙≤𝒍𝒂𝒕𝒆𝒓₂ : TwoCellExpr
  𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₁∘𝒇𝒐𝒓𝒆𝒗𝒆𝒓₁≤𝟙 : TwoCellExpr
  𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₂∘𝒇𝒐𝒓𝒆𝒗𝒆𝒓₂≤𝟙 : TwoCellExpr
  ann_∈_⇒_ : TwoCellExpr → ModalityExpr m m₂ → ModalityExpr m m₂ → TwoCellExpr
    -- ^ Used to annotate a 2-cell with its domain and codomain. 


--------------------------------------------------
-- Printing mode and modality expressions (mostly for type errors)

show-mode : ModeExpr → String
show-mode ★ = "★"
show-mode ω = "ω"
show-mode ω×ω = "ω×ω"

show-modality : ModalityExpr m₁ m₂ → String
show-modality 𝟙 = "𝟙"
show-modality (μ ⓜ ρ) = show-modality μ ++ " ⓜ " ++ show-modality ρ
show-modality constantly = "constantly"
show-modality forever = "forever"
show-modality later = "later"
show-modality 𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₁ = "𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₁"
show-modality 𝒇𝒐𝒓𝒆𝒗𝒆𝒓₁ = "𝒇𝒐𝒓𝒆𝒗𝒆𝒓₁"
show-modality 𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₂ = "𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚₂"
show-modality 𝒇𝒐𝒓𝒆𝒗𝒆𝒓₂ = "𝒇𝒐𝒓𝒆𝒗𝒆𝒓₂"
show-modality 𝒍𝒂𝒕𝒆𝒓₁ = "𝒍𝒂𝒕𝒆𝒓₁"
show-modality 𝒍𝒂𝒕𝒆𝒓₂ = "𝒍𝒂𝒕𝒆𝒓₂"


--------------------------------------------------
-- Interpretation of modes and modalities in the presheaf model

⟦_⟧mode : ModeExpr → BaseCategory
⟦ ★ ⟧mode = M.★×★
⟦ ω ⟧mode = M.ω×★
⟦ ω×ω ⟧mode = M.ω×ω

-- ⟦_⟧modality : ModalityExpr m₁ m₂ → Modality ⟦ m₁ ⟧mode ⟦ m₂ ⟧mode
-- ⟦ 𝟙 ⟧modality = M.𝟙
-- ⟦ μ ⓜ ρ ⟧modality = ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
-- ⟦ constantly ⟧modality = M.constantly
-- ⟦ forever ⟧modality = M.forever
-- ⟦ later ⟧modality = M.later
-- ⟦ 𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚 ⟧modality = M.𝒄𝒐𝒏𝒔𝒕𝒂𝒏𝒕𝒍𝒚
-- ⟦ 𝒇𝒐𝒓𝒆𝒗𝒆𝒓 ⟧modality = M.𝒇𝒐𝒓𝒆𝒗𝒆𝒓
-- ⟦ 𝒍𝒂𝒕𝒆𝒓₁ ⟧modality = M.𝒍𝒂𝒕𝒆𝒓₁
-- ⟦ 𝒍𝒂𝒕𝒆𝒓₂ ⟧modality = M.𝒍𝒂𝒕𝒆𝒓₂
