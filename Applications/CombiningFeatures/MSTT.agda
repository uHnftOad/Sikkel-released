--------------------------------------------------
-- Reexporting the instance of MSTT for guarded recursion
--------------------------------------------------
open import MSTT.Parameter.ModeTheory

module Applications.CombiningFeatures.MSTT (mt : ModeTheory) where

open import Applications.CombiningFeatures.MSTT.TypeExtension
open import Applications.CombiningFeatures.MSTT.TermExtension

open import Applications.CombiningFeatures.MSTT.ModeTheory public
open import Applications.CombiningFeatures.MSTT.Syntax.Type public
open import MSTT.Syntax.Context GR-mode-theory GR-ty-ext public
open import Applications.CombiningFeatures.MSTT.Syntax.Term public
open import MSTT.TCMonad public using (type-error ; ok)
open import MSTT.TypeChecker.ResultType GR-mode-theory GR-ty-ext public
open import MSTT.TypeChecker GR-mode-theory GR-ty-ext GR-tm-ext public
open import MSTT.BasicOperations GR-mode-theory GR-ty-ext GR-tm-ext public
