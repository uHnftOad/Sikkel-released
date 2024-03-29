--------------------------------------------------
-- Reexporting the syntax for types in guarded recursive type theory
--   + definition of some synonyms.
--------------------------------------------------
open import MSTT.Parameter.ModeTheory

module Applications.CombiningFeatures.MSTT.Syntax.Type (mt : ModeTheory) where

open import Data.Product
open import Data.Unit

open import Applications.CombiningFeatures.MSTT.ModeTheory mt
open import Applications.CombiningFeatures.MSTT.TypeExtension mt 


import MSTT.Syntax.Type GR-mode-theory GR-ty-ext as GRType
open GRType using (Ext)
open GRType public hiding (Ext)

▻ : TyExpr ω → TyExpr ω
▻ T = ⟨ later ∣ T ⟩

pattern GStream A = Ext GStream-code (A , tt)
