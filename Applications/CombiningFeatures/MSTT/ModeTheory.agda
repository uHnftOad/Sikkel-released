--------------------------------------------------
-- Definition of the mode theory for guarded recursive type theory
--------------------------------------------------
open import MSTT.Parameter.ModeTheory

module Applications.CombiningFeatures.MSTT.ModeTheory (mt : ModeTheory) where

open import Model.Modality using (≅ᵐ-refl)

open import Applications.CombiningFeatures.MSTT.ModeTheory.TwoCells mt

-- Re-exporting the expressions and equality tests of the mode theory.
open import Applications.CombiningFeatures.MSTT.ModeTheory.Expressions mt public
open import Applications.CombiningFeatures.MSTT.ModeTheory.Equivalence mt public using (_≟mode_; _≃ᵐ?_)

GR-mode-theory : ModeTheory
ModeTheory.ModeExpr GR-mode-theory = ModeExpr
ModeTheory.show-mode GR-mode-theory = show-mode
ModeTheory.⟦_⟧mode GR-mode-theory = ⟦_⟧mode
ModeTheory._≟mode_ GR-mode-theory = _≟mode_
ModeTheory.ModalityExpr GR-mode-theory = ModalityExpr
ModeTheory.𝟙 GR-mode-theory = 𝟙
ModeTheory._ⓜ_ GR-mode-theory = _ⓜ_
ModeTheory.show-modality GR-mode-theory = show-modality
ModeTheory.⟦_⟧modality GR-mode-theory = ⟦_⟧modality
ModeTheory.𝟙-interpretation GR-mode-theory = ≅ᵐ-refl
ModeTheory.ⓜ-interpretation GR-mode-theory = λ _ _ → ≅ᵐ-refl
ModeTheory._≃ᵐ?_ GR-mode-theory = _≃ᵐ?_
ModeTheory.TwoCellExpr GR-mode-theory = TwoCellExpr
ModeTheory.id-cell GR-mode-theory = id-cell
ModeTheory.⟦_∈_⇒_⟧two-cell GR-mode-theory = check-two-cell
