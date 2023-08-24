--------------------------------------------------
-- Definition of functors + some examples
--------------------------------------------------

module Model.Functor where

-- open import Data.Nat using (ℕ; _≤_)
-- open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Function using (_∘_; id)
open import Level renaming (zero to lzero; suc to lsuc)

open import Model.BaseCategory

open BaseCategory

infixl 5 _∘ᶠ_
infixl 6 _⊗ᶠ_
infixl 5 _⒩ᵛ_
infixl 5 _⒩ʰ_
infix 1 _≅ᶠ_
infixl 6 _⊗ⁿᵗ_

private
  variable
    C D E U V W : BaseCategory

--------------------------------------------------
-- Functors between two base categories

record Functor (C D : BaseCategory) : Set where
  open BaseCategory
  field
    ob : Ob C → Ob D
    hom : ∀ {x y} → Hom C x y → Hom D (ob x) (ob y)
    id-law : ∀ {x} → hom (hom-id C {x}) ≡ hom-id D {ob x}
    comp-law : ∀ {x y z} {f : Hom C x y} {g : Hom C y z} →
               hom (g ∙[ C ] f) ≡ (hom g) ∙[ D ] (hom f)

open Functor public

-- Composition of functors
_∘ᶠ_ : Functor D E → Functor C D → Functor C E
ob (G ∘ᶠ F) = ob G ∘ ob F
hom (G ∘ᶠ F) = hom G ∘ hom F
id-law (G ∘ᶠ F) = trans (cong (hom G) (id-law F)) (id-law G)
comp-law (G ∘ᶠ F) = trans (cong (hom G) (comp-law F)) (comp-law G)

-- Identity functors
id-functor : Functor C C
ob id-functor = id
hom id-functor = id
id-law id-functor = refl
comp-law id-functor = refl

flip-functor : Functor (C ⊗ D) (D ⊗ C)
ob flip-functor [ c , d ] = [ d , c ]
hom flip-functor [ f , g ] = [ g , f ]
id-law flip-functor = refl
comp-law flip-functor = refl

-- Natural transformations between functors
record NatTransf (F G : Functor C D) : Set₁ where
  constructor MkNT
  field
    transf-op : (c : Ob C) → Hom D (ob F c) (ob G c)
    naturality : {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} → hom G f ∙[ D ] transf-op c₁ ≡ transf-op c₂ ∙[ D ] hom F f

open NatTransf public

id-nt : {F : Functor C D} → NatTransf F F
id-nt {D = D} = MkNT (λ _ → hom-id D) (hom-idⁱ D) 

-- Vertical composition of natural transformations.
_⒩ᵛ_ : {F G H : Functor C D} → NatTransf G H → NatTransf F G → NatTransf F H
transf-op (_⒩ᵛ_ {D = D} β α) c = (transf-op β c) ∙[ D ] (transf-op α c)
naturality (_⒩ᵛ_ {D = D} β α) = trans (sym (∙assoc D)) 
                                    (trans (cong (λ g → category-composition D g (transf-op α _)) (naturality β)) 
                                    (trans (∙assoc D) 
                                    (trans (cong (category-composition D (transf-op β _)) (naturality α)) 
                                            (sym (∙assoc D)))))

-- Horizontal composition of natural transformations
_⒩ʰ_ : {G G' : Functor D E} {F F' : Functor C D} →
           NatTransf G G' → NatTransf F F' → NatTransf (G ∘ᶠ F) (G' ∘ᶠ F')
transf-op (_⒩ʰ_ {E = E} {G = G} {F' = F'} β α) c = transf-op β (ob F' c) ∙[ E ] hom G (transf-op α c)
naturality (_⒩ʰ_ {E = E} {G = G} {G'} {F} {F'} β α) {c₁} {c₂} {f} = 
  trans (cong (category-composition E (hom G' (hom F' f))) (sym (naturality β)))
 (trans (sym (∙assoc E))
 (trans (cong (λ h → category-composition E h (transf-op β (ob F c₁))) (sym (comp-law G')))
 (trans (naturality β)
 (trans (cong (λ h → category-composition E (transf-op β (ob F' c₂)) (hom G h))  (naturality α))
 (trans (cong (category-composition E (transf-op β (ob F' c₂))) (comp-law G))
        (sym (∙assoc E))))))) 

-- Natural isomorphisms between functors
record _≅ᶠ_ (F G : Functor C D) : Set₁ where
  field
    from : NatTransf F G
    to : NatTransf G F
    isoˡ : {c : Ob C} → transf-op to c ∙[ D ] transf-op from c ≡ hom-id D
    isoʳ : {c : Ob C} → transf-op from c ∙[ D ] transf-op to c ≡ hom-id D

open _≅ᶠ_ public

reflᶠ : {F : Functor C D} → F ≅ᶠ F
from (reflᶠ {D = D}) = MkNT (λ _ → hom-id D) (hom-idⁱ D)
to (reflᶠ {D = D}) = MkNT (λ _ → hom-id D) (hom-idⁱ D)
isoˡ (reflᶠ {D = D}) = hom-idˡ D
isoʳ (reflᶠ {D = D}) = hom-idˡ D

symᶠ : {F G : Functor C D} → F ≅ᶠ G → G ≅ᶠ F
from (symᶠ F=G) = MkNT (λ c → transf-op (to F=G) c) (naturality (to F=G))
to (symᶠ F=G) = MkNT (λ c → transf-op (from F=G) c) (naturality (from F=G))
isoˡ (symᶠ F=G) = isoʳ F=G
isoʳ (symᶠ F=G) = isoˡ F=G

transᶠ : {F G H : Functor C D} → F ≅ᶠ G → G ≅ᶠ H → F ≅ᶠ H
from (transᶠ F=G G=H) = from G=H ⒩ᵛ from F=G
to (transᶠ F=G G=H) = to F=G ⒩ᵛ to G=H
isoˡ (transᶠ {D = D} F=G G=H) = trans (∙assoc D) 
                               (trans (cong (category-composition D (transf-op (to F=G) _)) 
                                            (trans (sym (∙assoc D)) 
                                            (trans (cong (λ g → category-composition D g (transf-op (from F=G) _)) (isoˡ G=H))
                                                  (hom-idˡ D))))
                                      (isoˡ F=G))
isoʳ (transᶠ {D = D} F=G G=H) = trans (∙assoc D) 
                               (trans (cong (category-composition D (transf-op (from G=H) _)) 
                                            (trans (sym (∙assoc D)) 
                                            (trans (cong (λ g → category-composition D g (transf-op (to G=H) _)) (isoʳ F=G))
                                                  (hom-idˡ D))))
                                      (isoʳ G=H))

id-functor-unitˡ : (F : Functor C D) → id-functor ∘ᶠ F ≅ᶠ F
from (id-functor-unitˡ {D = D} F) = MkNT (λ _ → hom-id D) (hom-idⁱ D)
to (id-functor-unitˡ {D = D} F) = MkNT (λ _ → hom-id D) (hom-idⁱ D)
isoˡ (id-functor-unitˡ {D = D} F) = hom-idˡ D 
isoʳ (id-functor-unitˡ {D = D} F) = hom-idˡ D

id-functor-unitʳ : (F : Functor C D) → F ∘ᶠ id-functor ≅ᶠ F
from (id-functor-unitʳ {D = D} F) = MkNT (λ _ → hom-id D) (hom-idⁱ D)
to (id-functor-unitʳ {D = D} F) = MkNT (λ _ → hom-id D) (hom-idⁱ D)
isoˡ (id-functor-unitʳ {D = D} F) = hom-idˡ D 
isoʳ (id-functor-unitʳ {D = D} F) = hom-idˡ D

-- ∘ᶠ-assoc : 

-- ∘ᶠ-congˡ : (G : Functor D E) → {F F' : Functor C D} → F ≅ⁿ F' → G ∘ᶠ F ≅ⁿ G ∘ᶠ F'

-- ∘ᶠ-congʳ : 


--------------------------------------------------
-- Morphisms/1-cells in the product category Cat × Cat

_⊗ᶠ_ : Functor C D → Functor V W → Functor (C ⊗ V) (D ⊗ W)
ob (F ⊗ᶠ G) [ c , v ] = [ ob F c , ob G v ]
hom (F ⊗ᶠ G) [ f , g ] = [ hom F f , hom G g ]
id-law (F ⊗ᶠ G) = ×-≡,≡→≡ [ id-law F , id-law G ]
comp-law (F ⊗ᶠ G) = ×-≡,≡→≡ [ comp-law F , comp-law G ]

⊗ᶠ-id : id-functor {C} ⊗ᶠ id-functor {V} ≅ᶠ id-functor {C ⊗ V}
from (⊗ᶠ-id {C} {V}) = MkNT (λ _ → [ hom-id C , hom-id V ]) (×-≡,≡→≡ [ hom-idⁱ C , hom-idⁱ V ])
to (⊗ᶠ-id {C} {V}) = MkNT (λ _ → [ hom-id C , hom-id V ]) (×-≡,≡→≡ [ hom-idⁱ C , hom-idⁱ V ])
isoˡ (⊗ᶠ-id {C} {V}) = ×-≡,≡→≡ [ hom-idˡ C , hom-idˡ V ]
isoʳ (⊗ᶠ-id {C} {V}) = ×-≡,≡→≡ [ hom-idˡ C , hom-idˡ V ]

⊗ᶠ-ptwise-comp : (G : Functor D E) (F : Functor C D) (K : Functor V W) (H : Functor U V) → (G ⊗ᶠ K) ∘ᶠ (F ⊗ᶠ H) ≅ᶠ (G ∘ᶠ F) ⊗ᶠ (K ∘ᶠ H)
from (⊗ᶠ-ptwise-comp {E = E} {W = W} _ _ _ _) = MkNT (λ _ → [ hom-id E , hom-id W ]) (×-≡,≡→≡ [ hom-idⁱ E , hom-idⁱ W ])
to (⊗ᶠ-ptwise-comp {E = E} {W = W} _ _ _ _) = MkNT (λ _ → [ hom-id E , hom-id W ]) (×-≡,≡→≡ [ hom-idⁱ E , hom-idⁱ W ])
isoˡ (⊗ᶠ-ptwise-comp {E = E} {W = W} _ _ _ _) = ×-≡,≡→≡ [ hom-idˡ E , hom-idˡ W ]
isoʳ (⊗ᶠ-ptwise-comp {E = E} {W = W} _ _ _ _) = ×-≡,≡→≡ [ hom-idˡ E , hom-idˡ W ]

⊗ᶠ-congˡ : (F : Functor C D) → {G G' : Functor V W} → G ≅ᶠ G' → F ⊗ᶠ G ≅ᶠ F ⊗ᶠ G'
from (⊗ᶠ-congˡ {D = D} F G=G') = MkNT (λ _ → [ hom-id D , transf-op (from G=G') _ ]) (×-≡,≡→≡ [ hom-idⁱ D , naturality (from G=G') ])
to (⊗ᶠ-congˡ {D = D} F G=G') = MkNT (λ _ → [ hom-id D , transf-op (to G=G') _ ]) (×-≡,≡→≡ [ hom-idⁱ D , naturality (to G=G') ])
isoˡ (⊗ᶠ-congˡ {D = D} F G=G') = ×-≡,≡→≡ [ hom-idˡ D , isoˡ G=G' ]
isoʳ (⊗ᶠ-congˡ {D = D} F G=G') = ×-≡,≡→≡ [ hom-idˡ D , isoʳ G=G' ]

⊗ᶠ-congʳ : {F F' : Functor C D} → (G : Functor V W) → F ≅ᶠ F' → F ⊗ᶠ G ≅ᶠ F' ⊗ᶠ G
from (⊗ᶠ-congʳ {W = W} G F=F') = MkNT (λ _ → [ transf-op (from F=F') _ , hom-id W ]) (×-≡,≡→≡ [ naturality (from F=F') , hom-idⁱ W ])
to (⊗ᶠ-congʳ {W = W} G F=F') = MkNT (λ _ → [ transf-op (to F=F') _ , hom-id W ]) (×-≡,≡→≡ [ naturality (to F=F') , hom-idⁱ W ])
isoˡ (⊗ᶠ-congʳ {W = W} G F=F') = ×-≡,≡→≡ [ isoˡ F=F' , hom-idˡ W ]
isoʳ (⊗ᶠ-congʳ {W = W} G F=F') = ×-≡,≡→≡ [ isoʳ F=F' , hom-idˡ W ]

_⊗ⁿᵗ_ : {F F' : Functor C D} {G G' : Functor V W} → NatTransf F F' → NatTransf G G' → NatTransf (F ⊗ᶠ G) (F' ⊗ᶠ G')
transf-op (_⊗ⁿᵗ_ α β) [ c , v ] = [ transf-op α c , transf-op β v ]
naturality (_⊗ⁿᵗ_ α β) = ×-≡,≡→≡ [ naturality α , naturality β ]

-- ⊗ᶠ-projˡ : {F F' : Functor C D} {G G' : Functor V W} → F ⊗ᶠ G ≅ᶠ F' ⊗ᶠ G' → F ≅ᶠ F'
-- from (⊗ᶠ-projˡ {F} {F'} {G} {G'} F×G=F'×G') = {!   !}
-- to (⊗ᶠ-projˡ {F} {F'} {G} {G'} F×G=F'×G') = {!   !}
-- isoˡ (⊗ᶠ-projˡ {F} {F'} {G} {G'} F×G=F'×G') = {!   !}
-- isoʳ (⊗ᶠ-projˡ {F} {F'} {G} {G'} F×G=F'×G') = {!   !}

-- ⊗ᶠ-projʳ : {F F' : Functor C D} {G G' : Functor V W} → 

-- ⊗ᶠ-flip-cong : {F F' : Functor C D} {G G' : Functor V W} → 


--------------------------------------------------
-- Examples

-- The functor that generates `later`
ω-suc : Functor ω ω
ob ω-suc n = suc n
hom ω-suc m≤n = s≤s m≤n
id-law ω-suc = refl
comp-law ω-suc = refl

-- The functor that generates `forever`
𝒵 : {C : BaseCategory} → Functor C ★
ob 𝒵 _ = tt
hom 𝒵 _ = tt
id-law 𝒵 = refl
comp-law 𝒵 = refl

𝒵-id : 𝒵 {★} ≅ᶠ id-functor
from 𝒵-id = MkNT (λ _ → tt) refl
to 𝒵-id = MkNT (λ _ → tt) refl
isoˡ 𝒵-id = refl
isoʳ 𝒵-id = refl

𝒵∘functor=𝒵 : {C D : BaseCategory} (F : Functor C D) → 𝒵 ∘ᶠ F ≅ᶠ 𝒵
from (𝒵∘functor=𝒵 F) = MkNT (λ _ → tt) refl
to (𝒵∘functor=𝒵 F) = MkNT (λ _ → tt) refl
isoˡ (𝒵∘functor=𝒵 F) = refl
isoʳ (𝒵∘functor=𝒵 F) = refl 

𝒬 : Functor ★ ω
ob 𝒬 _ = zero
hom 𝒬 _ = hom-id ω
id-law 𝒬 = refl
comp-law 𝒬 = refl
