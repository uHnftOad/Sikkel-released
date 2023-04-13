--------------------------------------------------
-- Reexporting the syntax for terms in guarded recursive type theory
--   + definition of some synonyms.
--------------------------------------------------
open import MSTT.Parameter.ModeTheory

module Applications.CombiningFeatures.MSTT.Syntax.Term (mt : ModeTheory) where

open import Data.Product
open import Data.Unit

open import Applications.CombiningFeatures.MSTT.ModeTheory mt 
open import Applications.CombiningFeatures.MSTT.TypeExtension mt 
open import Applications.CombiningFeatures.MSTT.TermExtension mt


import MSTT.Syntax.Term GR-mode-theory GR-ty-ext GR-tm-ext as GRTerm
open GRTerm using (ext)
open GRTerm public hiding (ext)

pattern constantly-if c t f = ext constantly-if-code (c , (t , (f , tt)))

infixr 4 löb[later∣_∈_]_
pattern löb[later∣_∈_]_ x T t = ext (löb-code x T) (t , tt)

pattern g-cons A = ext (g-cons-code A) tt
pattern g-head A = ext (g-head-code A) tt
pattern g-tail A = ext (g-tail-code A) tt
