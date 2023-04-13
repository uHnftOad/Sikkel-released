open import Model.BaseCategory

module Applications.CombiningFeatures.Model.Modalities.Bundles (V : BaseCategory) where

open import Model.CwF-Structure.ContextFunctor
open import Model.Modality
open import Applications.CombiningFeatures.Model.Modalities.Later V hiding (ω×V)
open import Applications.CombiningFeatures.Model.Modalities.Constantly V hiding (ω×V)
open import Applications.CombiningFeatures.Model.Modalities.Forever V hiding (ω×V)

ω×V : BaseCategory
ω×V = ω ⊗ V


--------------------------------------------------
-- Define the `later` modality

earlier-functor : CtxFunctor ω×V ω×V
ctx-op earlier-functor = ◄
is-functor earlier-functor = ◄-is-functor

later : Modality ω×V ω×V
ctx-functor later = earlier-functor
⟨_∣_⟩ later = ▻
mod-cong later = ▻-cong
mod-natural later = ▻-natural
mod-intro later = next
mod-intro-cong later = next-cong
mod-intro-natural later = next-natural
mod-intro-ι later = next-ι
mod-elim later = prev
mod-elim-cong later = prev-cong
mod-β later = prev-next
mod-η later = next-prev


--------------------------------------------------
-- Define the `constantly` modality

now-functor : CtxFunctor ω×V V
ctx-op now-functor = now
is-functor now-functor = now-is-functor

constantly : Modality V ω×V
ctx-functor constantly = now-functor
⟨_∣_⟩ constantly = constantly-ty
mod-cong constantly = constantly-ty-cong
mod-natural constantly = constantly-ty-natural
mod-intro constantly = constantly-tm
mod-intro-cong constantly = constantly-tm-cong
mod-intro-natural constantly = constantly-tm-natural
mod-intro-ι constantly = constantly-tm-ι
mod-elim constantly = unconstantly-tm
mod-elim-cong constantly = unconstantly-tm-cong
mod-β constantly = constantly-ty-β
mod-η constantly = constantly-ty-η


--------------------------------------------------
-- Define the `forever` modality

constantly-ctx-functor : CtxFunctor V ω×V
ctx-op constantly-ctx-functor = constantly-ctx
is-functor constantly-ctx-functor = constantly-ctx-is-functor

forever : Modality ω×V V
ctx-functor forever = constantly-ctx-functor
⟨_∣_⟩ forever = forever-ty
mod-cong forever = forever-ty-cong
mod-natural forever = forever-ty-natural
mod-intro forever = forever-tm
mod-intro-cong forever = forever-tm-cong
mod-intro-natural forever = forever-tm-natural
mod-intro-ι forever = forever-tm-ι
mod-elim forever = unforever-tm
mod-elim-cong forever = unforever-tm-cong
mod-β forever = forever-ty-β
mod-η forever = forever-ty-η
