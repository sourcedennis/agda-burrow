{-# OPTIONS --safe #-}

open import Burrow.Primitives
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)

module Burrow.WellFormed.Derived
  {arch : Arch}
  {ex : Execution {arch}}
  (wf : WellFormed ex)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst; subst₂) renaming (sym to ≡-sym; trans to ≡-trans)
open import Function using (_∘_)
open import Data.Nat using (zero)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂; map₂)
open import Data.Sum as S using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (IsStrictTotalOrder)
open import Relation.Binary renaming (IsStrictTotalOrder to STO)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_; _∷ʳ_)
open import Function using (flip)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Burrow.Internal.Helpers
open import Burrow.Primitives
open import Burrow.Event.Core {arch}
open import Burrow.Event.Pred
open import Burrow.Event.Rel
open import Burrow.Event.Properties
open import Burrow.Execution.Derived ex

open Arch arch
open Execution ex
open WellFormed wf


-- ## Type Aliases

_ˡ∈ex : Rel₀ Event → Set
_ˡ∈ex R =
    {x y : Event}
  → R x y
    ----------------
  → x ∈ events

_ʳ∈ex : Rel₀ Event → Set
_ʳ∈ex R =
    {x y : Event}
  → R x y
    ----------------
  → y ∈ events


udr[_]∈ex : Rel₀ Event → Set
udr[_]∈ex R =
    {x : Event}
  → x ∈ udr R
    -----------
  → x ∈ events


private
  lr→udr : {R : Rel₀ Event}
    → R ˡ∈ex
    → R ʳ∈ex
      -----------
    → udr[ R ]∈ex
  lr→udr Rˡ∈ex Rʳ∈ex (inj₁ (_ , po[xy])) = Rˡ∈ex po[xy]
  lr→udr Rˡ∈ex Rʳ∈ex (inj₂ (_ , po[xy])) = Rʳ∈ex po[xy]


-- ## Well-formedness Helpers: Events Membership

poˡ∈ex : po ˡ∈ex
poˡ∈ex = ⇔₁-apply-⊆₁ po-elements ∘ take-udrˡ po

poʳ∈ex : po ʳ∈ex
poʳ∈ex = ⇔₁-apply-⊆₁ po-elements ∘ take-udrʳ po

po∈ex : udr[ po ]∈ex
po∈ex = lr→udr poˡ∈ex poʳ∈ex

piˡ∈ex : po-imm ˡ∈ex
piˡ∈ex (po[xy] , _) = poˡ∈ex po[xy]

piʳ∈ex : po-imm ʳ∈ex
piʳ∈ex (po[xy] , _) = poʳ∈ex po[xy]

coˡ∈ex : co ˡ∈ex
coˡ∈ex {_} {y} co[xy] = ⊆₁-apply co-elements (inj₁ (y , co[xy]))

coʳ∈ex : co ʳ∈ex
coʳ∈ex {x} {_} co[xy] = ⊆₁-apply co-elements (inj₂ (x , co[xy]))

rfˡ∈ex : rf ˡ∈ex
rfˡ∈ex {_} {y} rf[xy] = ⊆₁-apply rf-elements (inj₁ (y , rf[xy]))

rfʳ∈ex : rf ʳ∈ex
rfʳ∈ex {x} {_} rf[xy] = ⊆₁-apply rf-elements (inj₂ (x , rf[xy]))

frˡ∈ex : fr ˡ∈ex
frˡ∈ex {_} {y} (rf[zx] ⨾[ z ]⨾ co[zy]) = rfʳ∈ex rf[zx]

frʳ∈ex : fr ʳ∈ex
frʳ∈ex {x} {_} (rf[zx] ⨾[ z ]⨾ co[zy]) = coʳ∈ex co[zy]

rmwˡ∈ex : rmw ˡ∈ex
rmwˡ∈ex {x} {y} rmw[xy] with ⊆₂-apply rmw-def rmw[xy]
... | (po[xy] , _) = ⇔₁-apply-⊆₁ po-elements (inj₁ (y , po[xy]))

rmwʳ∈ex : rmw ʳ∈ex
rmwʳ∈ex {x} {y} rmw[xy] with ⊆₂-apply rmw-def rmw[xy]
... | (po[xy] , _) = ⇔₁-apply-⊆₁ po-elements (inj₂ (x , po[xy]))

rmwˡ-r :
    {x : Event}
  → x ∈ dom rmw
    -----------------
  → EvRₜ trmw x
rmwˡ-r (y , rmw[xy]) = ×₂-applyˡ rmw-r×w rmw[xy]

rmwʳ-w :
    {x : Event}
  → x ∈ codom rmw
    ------------------
  → EvWₜ trmw x
rmwʳ-w (y , rmw[yx]) = ×₂-applyʳ rmw-r×w rmw[yx]


-- ## Well-formedness: Relation (co-)domains

pi-elements : udr po-imm ⇔₁ events
pi-elements = ⇔₁-intro ⊆-proof ⊇-proof
  where
  ⊆-proof : udr po-imm ⊆₁ events
  ⊆-proof = ⊆₁-trans (udr-preserves-⊆ imm-⊆₂) (⇔₁-to-⊆₁ po-elements)

  ⊇-proof : events ⊆₁ udr po-imm
  ⊇-proof = ⊆₁-trans (⇔₁-to-⊇₁ po-elements) (⇔₁-to-⊆₁ (splittable-imm-udr po-splittable))

fr-elements : udr fr ⊆₁ events
fr-elements =
  begin⊆₁
    udr fr
  ⊆₁⟨ udr-preserves-⊆ (≡-to-⊆₂ refl) ⟩
    udr (flip rf ⨾ co)
  ⊆₁⟨ udr-combine-⨾ ⟩
    udr (flip rf) ∪₁ udr co
  ⊆₁⟨ ⇔₁-to-⊆₁ (∪₁-substˡ (⇔₁-sym udr-flip)) ⟩
    udr rf ∪₁ udr co
  ⊆₁⟨ ∪₁-substˡ-⊆₁ rf-elements ⟩
    events ∪₁ udr co
  ⊆₁⟨ ∪₁-substʳ-⊆₁ co-elements ⟩
    events ∪₁ events
  ⊆₁⟨ ⇔₁-to-⊆₁ ∪₁-idem ⟩
    events
  ⊆₁∎

-- | Derived definition of the (co-)domain of 'fr'.
fr-r×w : fr ⊆₂ EvR ×₂ EvW
fr-r×w = 
  begin⊆₂
    fr
  ⊆₂⟨ ⊆₂-refl ⟩
    flip rf ⨾ co
  ⊆₂⟨ ⨾-substʳ-⊆₂ co-w×w ⟩
    flip rf ⨾ ( EvW ×₂ EvW )
  ⊆₂⟨ ⨾-substˡ-⊆₂ (×₂-flip-⊆₂ rf-w×r) ⟩
    ( EvR ×₂ EvW ) ⨾ ( EvW ×₂ EvW )
  ⊆₂⟨ ×₂-combine-⨾ ⟩
    EvR ×₂ EvW
  ⊆₂∎

fr-sloc : fr ⊆₂ SameLoc
fr-sloc = 
  begin⊆₂
    fr
  ⊆₂⟨ ⊆₂-refl ⟩
    flip rf ⨾ co
  ⊆₂⟨ ⨾-substˡ-⊆₂ (flip-⊆₂ rf-sloc) ⟩
    flip SameLoc ⨾ co
  ⊆₂⟨ ⨾-substˡ-⊆₂ (flip-sym-⊆₂ sym-same-loc) ⟩
    SameLoc ⨾ co
  ⊆₂⟨ ⨾-substʳ-⊆₂ co-sloc ⟩
    SameLoc ⨾ SameLoc
  ⊆₂⟨ ⨾-trans-⊆₂ trans-same-loc ⟩
    SameLoc
  ⊆₂∎

rfe-w×r : rfe ⊆₂ ( EvW ×₂ EvR )
rfe-w×r = ⊆₂-trans (external⊆ rf) rf-w×r

coe-w×w : coe ⊆₂ ( EvW ×₂ EvW )
coe-w×w = ⊆₂-trans (external⊆ co) co-w×w

fre-r×w : fre ⊆₂ ( EvR ×₂ EvW )
fre-r×w = ⊆₂-trans (external⊆ fr) fr-r×w

rfi-w×r : rfi ⊆₂ ( EvW ×₂ EvR )
rfi-w×r = ⊆₂-trans (internal⊆ rf) rf-w×r

coi-w×w : coi ⊆₂ ( EvW ×₂ EvW )
coi-w×w = ⊆₂-trans (internal⊆ co) co-w×w

fri-r×w : fri ⊆₂ ( EvR ×₂ EvW )
fri-r×w = ⊆₂-trans (internal⊆ fr) fr-r×w


-- ## Well-formedness: Derived `po` properties

private

  po-shared-tid :
      {x y : Event}
    → (po[xy] : po x y)
      --------------------------------------------------------------
    → ∃[ tid ] (EvInit x ⊎ HasTid tid x) × (EvInit y ⊎ HasTid tid y)
  po-shared-tid         po[xy] with ⊆₂-apply po-stid po[xy]
  po-shared-tid {y = y} po[xy] | inj₁ (x-init , _) =
    case ev-init/tid y of
    λ{ (xopt₁ y-init _) → -- both are init events
         thread-id zero , inj₁ x-init , inj₁ y-init
     ; (xopt₂ _ (tid , y-tid)) →
         tid , inj₁ x-init , inj₂ y-tid
     }
  po-shared-tid         po[xy] | inj₂ (same-tid {tid} x-tid y-tid) = tid , inj₂ x-tid , inj₂ y-tid


po-shared-tid₂ :
    {x y z : Event}
  → po x y → po y z
    ------------------------------------------------------------------------------------------
  → ∃[ tid ] (EvInit x ⊎ HasTid tid x) × (EvInit y ⊎ HasTid tid y) × (EvInit z ⊎ HasTid tid z)
po-shared-tid₂ po[xy] po[yz] with po-shared-tid po[xy] | po-shared-tid po[yz]
po-shared-tid₂ po[xy] po[yz] | _ , _ , inj₁ ev-init | tid₂ , inj₁ ev-init , z-init/tid =
  (tid₂ , inj₁ (po-init-first po[xy] ev-init) , inj₁ ev-init , z-init/tid)
po-shared-tid₂ po[xy] po[yz] | tid₁ , x-init/tid₁ , inj₂ y-tid₁ | tid₂ , inj₂ y-tid₂ , inj₂ z-tid₂ =
  (tid₁ , x-init/tid₁ , inj₂ y-tid₁ , inj₂ (subst-tid (tid-unique y-tid₂ y-tid₁) z-tid₂))
-- impossible
po-shared-tid₂ {_} {y} po[xy] po[yz] | tid₁ , _ , inj₂ y-tid₁ | tid₂ , inj₁ y-init , _ =
  ⊥-elim (xopt₂-select₁ y-init (ev-init/tid y) (tid₁ , y-tid₁))
po-shared-tid₂ {x} {y} {z} po[xy] po[yz] | tid₁ , fst , inj₂ y-tid₁ | tid₂ , inj₂ y-tid₂ , inj₁ z-init =
  contradiction (po-init-first po[yz] z-init) (xopt₂-select₂ (tid₂ , y-tid₂) (ev-init/tid y))


po-shared-tid₂' :
    {x y z : Event}
  → po x z → po y z
    ------------------------------------------------------------------------------------------
  → ∃[ tid ] (EvInit x ⊎ HasTid tid x) × (EvInit y ⊎ HasTid tid y) × (EvInit z ⊎ HasTid tid z)
po-shared-tid₂' {x} {y} {z} po[xz] po[yz] with xopt₂-sum (ev-init/tid z)
... | inj₁ z-init        =
  thread-id zero , inj₁ (po-init-first po[xz] z-init) , inj₁ (po-init-first po[yz] z-init) , inj₁ z-init
... | inj₂ (tid , z-tid) = tid , lemma z-tid po[xz] , lemma z-tid po[yz] , inj₂ z-tid
  where
  lemma : {tid : ThreadId} {x : Event} → HasTid tid z → po x z → (EvInit x ⊎ HasTid tid x)
  lemma z-tid po[xy] with ⊆₂-apply po-stid po[xy]
  ... | inj₁ (x-init , _) = inj₁ x-init
  ... | inj₂ xy-stid = inj₂ (subst-stid (sym-same-tid xy-stid) z-tid)


lift∈ex : {ev : Event}
  → ev ∈ events
    -------------------------------------------------------
  → ∃[ tid ] WithPred ((EvInit ∪₁ HasTid tid) ∩₁ events)
lift∈ex {ev} ev∈ex = map₂ (λ τ → with-pred ev (τ , ev∈ex)) (lemma ev)
  where
  -- This lemma is crucial; We should /not/ pattern-match on `ev` in the `lift∈ex` scope.
  -- Then Agda cannot infer that `ev∈ex` is included without explicitly
  -- pattern-matching.
  lemma : (ev : Event) → ∃[ tid ] (EvInit ∪₁ HasTid tid) ev
  lemma (event-init _ _ _)    = thread-id zero , inj₁ ev-init
  lemma (event-skip _ tid)    = tid  , inj₂ has-tid-skip
  lemma (event-r _ tid _ _ _) = tid  , inj₂ has-tid-r
  lemma (event-w _ tid _ _ _) = tid  , inj₂ has-tid-w
  lemma (event-f _ tid _)     = tid  , inj₂ has-tid-f


po-same-tid :
    {x y : Event}
  → {tid₁ tid₂ : ThreadId}
  → HasTid tid₁ x
  → HasTid tid₂ y
  → po x y
    -------------
  → tid₁ ≡ tid₂
po-same-tid x-tid₁ y-tid₂ po[xy] with ⊆₂-apply po-stid po[xy]
po-same-tid {x} {y} {tid₁} x-tid₁ y-tid₂ po[xy] | inj₁ (x-init , _) =
  ⊥-elim (xopt₂-select₁ x-init (ev-init/tid x) (tid₁ , x-tid₁))
po-same-tid                x-tid₁ y-tid₂ po[xy] | inj₂ xy-sametid   =
  tid-unique (subst-stid xy-sametid x-tid₁) y-tid₂

po-tidʳ :
    {x y : Event}
  → {tid : ThreadId}
  → po x y
  → HasTid tid x
    ------------
  → HasTid tid y
po-tidʳ {x} {_} {tid} po[xy] x-tid with ⊆₂-apply po-stid po[xy]
... | inj₁ (x-init , _) = ⊥-elim (xopt₂-select₁ x-init (ev-init/tid x) (tid , x-tid))
... | inj₂ xy-stid = subst-stid xy-stid x-tid


events-dec : DecPred events
events-dec x with events-uid-dec (ev-uid x)
events-dec x | yes (y , y-uid-x , y∈dst) with ev-dec≡ x y
events-dec x | yes (.x , y-uid-x , y∈dst) | yes refl = yes y∈dst
events-dec x | yes (y , y-uid-x , y∈dst)  | no  x≢y  =
  no (λ{x∈dst → x≢y (unique-ids (ev-uid x) (ev-has-uid x , x∈dst) (y-uid-x , y∈dst))})
events-dec x | no ¬∃x = no (λ{x∈dst → ¬∃x (x , ev-has-uid x , x∈dst)})


-- | For any `x` and `y` it is decidable whether `po x y` holds or not.
po-dec : DecRel po
po-dec x y with events-dec x | events-dec y
po-dec x y | yes x∈ex | yes y∈ex with ev-init/tid x | ev-init/tid y
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ with po-tri (thread-id zero) (with-pred x (inj₁ x-init , x∈ex)) (with-pred y (inj₁ y-init , y∈ex))
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ | tri<  po[xy] _ _ = yes po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ | tri≈ ¬po[xy] _ _ = no ¬po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ | tri> ¬po[xy] _ _ = no ¬po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₂ _ (tid , y-tid) with po-tri tid (with-pred x (inj₁ x-init , x∈ex)) (with-pred y (inj₂ y-tid , y∈ex))
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₂ _ (tid , y-tid) | tri<  po[xy] _ _ = yes po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₂ _ (tid , y-tid) | tri> ¬po[xy] _ _ = no ¬po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ x-¬init x-tid  | xopt₁ y-init _ = no (λ po[xy] → ⊤prec⊥-invert po po-init-first po[xy] x-¬init y-init)
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) with tid-dec≡ tid₁ tid₂
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) | yes tid₁≡tid₂@refl with po-tri tid₁ (with-pred x (inj₂ x-tid₁ , x∈ex)) (with-pred y (inj₂ y-tid₂ , y∈ex))
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₁ , y-tid₂) | yes refl | tri<  po[xy] _ _ = yes po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₁ , y-tid₂) | yes refl | tri≈ ¬po[xy] _ _ = no ¬po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₁ , y-tid₂) | yes refl | tri> ¬po[xy] _ _ = no ¬po[xy]
po-dec x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) | no tid₁≢tid₂ = no (tid₁≢tid₂ ∘ po-same-tid x-tid₁ y-tid₂)
po-dec x y | yes x∈ex | no  y∉ex = no (contraposition poʳ∈ex y∉ex)
po-dec x y | no  x∉ex | yes y∈ex = no (contraposition poˡ∈ex x∉ex)
po-dec x y | no  x∉ex | no  y∉ex = no (contraposition poˡ∈ex x∉ex)


po-trans : Transitive po
po-trans = splittable-trans po-splittable


po-init-tri : Trichotomous _≡_ (filter-rel (EvInit ∩₁ events) po)
po-init-tri (with-pred x (x-init , x∈ex)) (with-pred y (y-init , y∈ex))
  with po-tri (thread-id zero) (with-pred x (inj₁ x-init , x∈ex)) (with-pred y (inj₁ y-init , y∈ex))
... | tri<  a ¬b   ¬c = tri< a (λ{refl → ¬c a}) ¬c
... | tri≈ ¬a refl ¬c = tri≈ ¬a refl ¬c
... | tri> ¬a ¬b    c = tri> ¬a (λ{refl → ¬a c}) c


po-thread-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel (HasTid tid ∩₁ events) po)
po-thread-tri tid (with-pred x (x-tid , x∈ex)) (with-pred y (y-tid , y∈ex))
  with po-tri tid (with-pred x (inj₂ x-tid , x∈ex)) (with-pred y (inj₂ y-tid , y∈ex))
... | tri<  a ¬b   ¬c = tri< a (λ{refl → ¬b refl}) ¬c
... | tri≈ ¬a refl ¬c = tri≈ ¬a refl ¬c
... | tri> ¬a ¬b    c = tri> ¬a (λ{refl → ¬b refl}) c


po-irreflexive : Irreflexive _≡_ po
po-irreflexive refl po[xx] =
  let (tid , x) = lift∈ex (poˡ∈ex po[xx])
  in tri-irreflexive (po-tri tid) {x} refl po[xx]

po-acyclic : Acyclic _≡_ po
po-acyclic refl po⁺[xx] =
  let po[xx] = ⊆₂-apply (⁺-trans-⊆₂ po-trans) po⁺[xx]
  in po-irreflexive refl po[xx]


-- ## Well-formedness: Derived `co` properties

co-irreflexive : Irreflexive _≡_ co
co-irreflexive {x} refl co[xx] =
  let x-w = ×₂-applyˡ co-w×w co[xx]
      (loc , x-loc) = ⊆₁-apply W⊆SomeLoc x-w
  in tri-irreflexive (co-tri loc) {x = with-pred x (x-w , x-loc , coˡ∈ex co[xx])} refl co[xx]

-- Coherence order is defined over same-location writes. Every location is initialised /exactly once/.
co-unique-init :
    {uid₁ uid₂ : UniqueId} {loc₁ loc₂ : Location} {val₁ val₂ : Value}
    ---------------------------------------------------------------
  → ¬ co (event-init uid₁ loc₁ val₁) (event-init uid₂ loc₂ val₂)
co-unique-init {uid₁} {uid₂} {loc₁} {loc₂} {val₁} {val₂} co[xy] with ⊆₂-apply co-sloc co[xy]
... | same-loc has-loc-init has-loc-init
  with wf-init-≤1 loc₁
         (ev-init , has-loc-init , x∈evs)
         (ev-init , has-loc-init , y∈evs)
  where
  x∈evs = coˡ∈ex co[xy]
  y∈evs = coʳ∈ex co[xy]
... | refl = co-irreflexive refl co[xy]


wf-init-co-≤1 : (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ udr co)
wf-init-co-≤1 loc (init-x , x-loc , x∈co) (init-y , y-loc , y∈co) =
  let x∈evs = ⊆₁-apply co-elements x∈co
      y∈evs = ⊆₁-apply co-elements y∈co
  in wf-init-≤1 loc (init-x , x-loc , x∈evs) (init-y , y-loc , y∈evs)


-- ## Well-formedness: Derived `rf` properties

rf-irreflexive : Irreflexive _≡_ rf
rf-irreflexive {x} refl rf[xx] =
  disjoint-r/w _ (×₂-applyʳ rf-w×r rf[xx] , ×₂-applyˡ rf-w×r rf[xx])


-- ## Well-formedness: Derived `fr` properties

fr-irreflexive : Irreflexive _≡_ fr
fr-irreflexive {x} refl fr[xx] =
  disjoint-r/w _ (×₂-applyˡ fr-r×w fr[xx] , ×₂-applyʳ fr-r×w fr[xx])


-- ## Well-formedness: Derived internal/external properties

-- | Law of excluded middle for internal/external relations
internal⊎external :
    (R : Rel₀ Event)
    -----------------------------------------------
  → R ⇔₂ internal R ∪₂ external R
internal⊎external R = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : R ⊆₂' internal R ∪₂ external R
  ⊆-proof x y Rxy with po-dec x y
  ⊆-proof x y Rxy | yes po[xy] = inj₁ (Rxy , po[xy])
  ⊆-proof x y Rxy | no ¬po[xy] = inj₂ (Rxy , ¬po[xy])

  ⊇-proof : internal R ∪₂ external R ⊆₂' R
  ⊇-proof x y (inj₁ (Rxy , _)) = Rxy
  ⊇-proof x y (inj₂ (Rxy , _)) = Rxy


po-thread-splittable : (tid : ThreadId) → SplittableOrder (filter-rel (HasTid tid ∩₁ events) po)
po-thread-splittable tid = filter-splittableʳ po-splittable (HasTid tid ∩₁ events) lemma
  where
  lemma : {x y : Event} → (HasTid tid ∩₁ events) x → po x y → (HasTid tid ∩₁ events) y
  lemma (x-tid , x∈ex) po[xy] = (po-tidʳ po[xy] x-tid , poʳ∈ex po[xy])


po-tidˡ :
    {tid : ThreadId} {x y : Event}
  → HasTid tid y
  → po x y
    ------------------------
  → (EvInit ∪₁ HasTid tid) x
po-tidˡ y-tid po[xy] with ⊆₂-apply po-stid po[xy]
... | inj₁ (x-init , _) = inj₁ x-init
... | inj₂ xy-stid      = inj₂ (subst-stid (sym-same-tid xy-stid) y-tid)


po-ex-splittable : (tid : ThreadId) → SplittableOrder (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events) po)
po-ex-splittable tid =
  filter-splittableˡ po-splittable ((EvInit ∪₁ HasTid tid) ∩₁ events) po-init/tidˡ
  where
  po-init/tidˡ : {tid : ThreadId} {x y : Event} → ((EvInit ∪₁ HasTid tid) ∩₁ events) y → po x y → ((EvInit ∪₁ HasTid tid) ∩₁ events) x
  po-init/tidˡ (inj₁ y-init , y∈ex) po[xy] = (inj₁ (po-init-first po[xy] y-init) , poˡ∈ex po[xy])
  po-init/tidˡ (inj₂ y-tid , y∈ex)  po[xy] = (po-tidˡ y-tid po[xy] , poˡ∈ex po[xy])


unsplit-poˡ :
    {x y z : Event}
  → ¬ EvInit x
  → po x z → po-imm x y
    -------------------------
  → y ≡ z ⊎ po y z
unsplit-poˡ {x} {y} {z} x-¬init po[xz] pi[xy] =
  let (tid , x-tid) = xopt₂-elim₁ x-¬init (ev-init/tid x)
      y-tid = po-tidʳ (proj₁ pi[xy]) x-tid
      z-tid = po-tidʳ po[xz] x-tid
  in
  case unsplitˡ (po-thread-tri tid) (po-thread-splittable tid)
         {x = with-pred x (x-tid , poˡ∈ex po[xz])}
         {y = with-pred y (y-tid , piʳ∈ex pi[xy])}
         {z = with-pred z (z-tid , poʳ∈ex po[xz])}
         po[xz] (⊆₂-apply imm-filter-⊆₂ pi[xy]) of
  (S.map₁ with-pred-≡)


unsplit-poʳ :
    {x y z : Event}
  → po x z → po-imm y z
    -------------------------
  → x ≡ y ⊎ po x y
unsplit-poʳ {x} {y} {z} po[xz] pi[yz] with po-shared-tid₂' po[xz] (proj₁ pi[yz])
... | tid , x-init/tid , y-init/tid , z-init/tid = 
  case unsplitʳ (po-tri tid) (po-ex-splittable tid)
         {x = with-pred x (x-init/tid , poˡ∈ex po[xz])}
         {y = with-pred y (y-init/tid , piˡ∈ex pi[yz])}
         {z = with-pred z (z-init/tid , poʳ∈ex po[xz])}
         po[xz] (⊆₂-apply imm-filter-⊆₂ pi[yz]) of
  S.map₁ with-pred-≡


private
  unique-po-pred :
      {tid : ThreadId}
      ---------------------------------------------
    → UniquePred ((EvInit ∪₁ HasTid tid) ∩₁ events)
  unique-po-pred =
    ∩₁-unique-pred
      (∪₁-unique-pred disjoint-init/tid init-unique has-tid-unique)
      events-unique


unsplit-po-triʳ :
    {x y z : Event}
  → po x z → po y z
    -----------------------------------
  → Tri (po x y) (x ≡ y) (po y x)
unsplit-po-triʳ {x} {y} {z} po[xz] po[yz]
  with po-shared-tid₂' po[xz] po[yz]
... | tid , x-init/tid , y-init/tid , z-init/tid
  with po-tri tid (with-pred x (x-init/tid , poˡ∈ex po[xz])) (with-pred y (y-init/tid , poˡ∈ex po[yz]))
... | tri<  po[xy] x≢y ¬po[yx] = tri<  po[xy] (with-pred-≢ unique-po-pred x≢y) ¬po[yx]
... | tri≈ ¬po[xy] x≡y ¬po[yx] = tri≈ ¬po[xy] (with-pred-≡ x≡y) ¬po[yx]
... | tri> ¬po[xy] x≢y  po[yx] = tri> ¬po[xy] (with-pred-≢ unique-po-pred x≢y)  po[yx]


w-rmw-dec : DecPred (EvWₜ {arch} trmw)
w-rmw-dec (event-w _ _ _ _ lab) with inspect (lab-w-tag lab)
... | tmov with≡ x = no (λ{(ev-w y) → mov≢rmw (≡-trans (≡-sym x) (≡-sym y))})
... | trmw with≡ x = yes (ev-w (≡-sym x))
w-rmw-dec (event-init _ _ _)  = no (λ{(ev-init ())})
w-rmw-dec (event-skip _ _)    = no (λ())
w-rmw-dec (event-r _ _ _ _ _) = no (λ())
w-rmw-dec (event-f _ _ _)     = no (λ())


po-immˡ :
    {x y z : Event}
  → po-imm x z → po-imm y z
    -----------------------------
  → x ≡ y
po-immˡ {x} {y} {z} pi[xz] pi[yz] with unsplit-poʳ (proj₁ pi[xz]) pi[yz]
... | inj₁ refl = refl
... | inj₂ po[xy] = ⊥-elim (proj₂ pi[xz] (y , po[xy] , [ proj₁ pi[yz] ]))


po-immʳ :
    {x y z : Event}
  → ¬ EvInit x
  → po-imm x y → po-imm x z
    -----------------------------
  → y ≡ z
po-immʳ {x} {y} {z} x-¬init pi[xy] pi[xz] with unsplit-poˡ x-¬init (proj₁ pi[xz]) pi[xy]
... | inj₁ y≡z    = y≡z
... | inj₂ po[yz] = ⊥-elim (proj₂ pi[xz] (y , proj₁ pi[xy] , [ po[yz] ]))


rmw-dec : DecRel rmw
rmw-dec x y with po-dec x y
rmw-dec x y | no ¬po[xy] = no (λ{rmw[xy] → ¬po[xy] (proj₁ (⊆₂-apply rmw-def rmw[xy]))})
rmw-dec x y | yes po[xy] with w-rmw-dec y
rmw-dec x y | yes po[xy] | yes y-w  =
  let (z , rmw[zy]) = ⇔₁-apply-⊇₁ rmw-w (poʳ∈ex po[xy] , y-w)
      pi[zy] = ⊆₂-apply rmw-def rmw[zy]
  in 
  case unsplit-poʳ po[xy] pi[zy] of
  λ{ (inj₁ x≡z) → yes (subst (λ τ → rmw τ y) (≡-sym x≡z) rmw[zy])
   ; (inj₂ po[xz]) → no (λ{rmw[xy] → proj₂ (⊆₂-apply rmw-def rmw[xy]) (z , po[xz] , [ proj₁ pi[zy] ])})
   }
rmw-dec x y | yes po[xy] | no y-¬w = no (y-¬w ∘ ×₂-applyʳ rmw-r×w)


pi-dec : DecRel po-imm
pi-dec x y with po-dec x y
pi-dec x y | yes po[xy] with ⇔₂-apply-⊆₂ po-splittable po[xy]
pi-dec x y | yes po[xy] | [ pi[xy] ] = yes pi[xy]
pi-dec x y | yes po[xy] | _∷_ {x} {z} pi[xz] pi⁺[zy] =
  no (λ{pi[xy] → proj₂ pi[xy] (z , proj₁ pi[xz] , ⁺-map _ proj₁ pi⁺[zy])})
pi-dec x y | no ¬po[xy] = no (λ{pi[xy] → ¬po[xy] (proj₁ pi[xy])})

po⁺⇒po :
    {x y : Event}
  → TransClosure po x y
  → po x y
po⁺⇒po = ⁺-join-trans po-trans

