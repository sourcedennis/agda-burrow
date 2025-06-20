{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.Framework.Definition using (GeneralFramework)


-- |
--
-- Also contains some definitions, but only those that strictly require the full
-- framework. (`Definitions` only requires `ev[⇐]`)
--
--
-- # Design Decision: Not WellFormed
--
-- Not all definitions in this module strictly pertain to WellFormedness. However, they
-- do all depend on the `GeneralFramework` (which `Definitions` above does not). Therefore,
-- we group all those definitions in this module.
module Burrow.Framework.WellFormed
  {archˢ archᵗ : Arch}
  {dst : Execution {archᵗ}}
  {dst-wf : WellFormed dst}
  (ψ : GeneralFramework archˢ dst-wf)
  where
  

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; cong) renaming (sym to ≡-sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (_∈_)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Relation.Binary.Construct.Closure.Reflexive using (ReflClosure; refl; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Burrow.Primitives
open import Burrow.Event.Core using (Event)
open import Burrow.Event.Pred
open import Burrow.Event.Rel
open import Burrow.Event.Properties
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.WellFormed.Derived
import Burrow.Framework.Primitives {archˢ} dst-wf as P


open Execution
open WellFormed dst-wf
open GeneralFramework ψ
open P ev[⇐]


-- # Mapping

-- ## Mapping: Primitives

private
  Eventˢ = Event {archˢ}
  Eventᵗ = Event {archᵗ}

  Predˢ = Pred₀ Eventˢ
  Predᵗ = Pred₀ Eventᵗ

  Relˢ = Rel₀ Eventˢ
  Relᵗ = Rel₀ Eventᵗ
  
  variable
    uid : UniqueId
    tid : ThreadId
    loc : Location
    val : Value
    
    xˢ yˢ : Eventˢ
    xᵗ yᵗ : Eventᵗ
    Pˢ : Predˢ
    Pᵗ : Predᵗ
    Rˢ Qˢ : Relˢ
    Rᵗ Qᵗ : Relᵗ


ev[$⇒]eq  :
    (x∈dst : xᵗ ∈ events dst) (y∈dst : yᵗ ∈ events dst)
  → ev[⇐] x∈dst ≡ ev[⇐] y∈dst
    -------------------------
  → xᵗ ≡ yᵗ
ev[$⇒]eq {x} {y} x∈dst y∈dst x[⇐]≡y[⇐] =
  let x[⇐]-has-uid : HasUid (ev-uid x) (ev[⇐] x∈dst)
      x[⇐]-has-uid = uid[⇐] x∈dst (ev-has-uid x)
      y[⇐]-has-uid : HasUid (ev-uid x) (ev[⇐] y∈dst)
      y[⇐]-has-uid = subst (HasUid (ev-uid x)) x[⇐]≡y[⇐] x[⇐]-has-uid
      y-has-uid : HasUid (ev-uid x) y
      y-has-uid = uid[$⇒] y∈dst y[⇐]-has-uid
  in unique-ids _ (ev-has-uid x , x∈dst) (y-has-uid , y∈dst)


-- |
--
-- # Design Decision: No explicit equivalence proof
--
-- An alternative definition, more consistent with the others, is as follows:
-- ```
-- {x y} → x∈dst → y∈dst → x ≡ y → ev[⇐] x∈dst ≡ ev[⇐] y∈dst
-- ```
-- Instead, we elected to omit the explicit equivalence proof, which results in
-- the current definition.
ev[⇐]eq : {x : Eventᵗ}
  → (x∈dst₁ x∈dst₂ : x ∈ events dst)
    --------------------------------
  → ev[⇐] x∈dst₁ ≡ ev[⇐] x∈dst₂
ev[⇐]eq {x} x∈dst₁ x∈dst₂ = cong ev[⇐] (events-unique x x∈dst₁ x∈dst₂)


ev[⇐$]eq : {x y : Eventˢ}
  → (x∈src : x ∈ src-events) (y∈src : y ∈ src-events)
  → ev[⇒] x∈src ≡ ev[⇒] y∈src
    -------------------------
  → x ≡ y
ev[⇐$]eq (dst-x , x∈dst , refl) (dst-x , y∈dst , refl) refl = ev[⇐]eq x∈dst y∈dst


-- | Starting with event `x` in the target: Mapping `x` to the source,
-- then mapping the result to the target, gives `x` again.
ev[⇐⇒] : {x : Eventᵗ}
  → (x∈dst : x ∈ events dst)
  → (x∈src : ev[⇐] {x} x∈dst ∈ src-events)
    ----------------------------------------
  → x ≡ ev[⇒] x∈src
ev[⇐⇒] x∈dst (y , y∈dst , ev[⇐]x≡ev[⇐]y) = ev[$⇒]eq x∈dst y∈dst ev[⇐]x≡ev[⇐]y


-- ## Mapping: Predicates

Init[⇒] : Pred[⇒]² EvInit
Init[⇒] = [$⇒]→₁[⇒] Init[$⇒]

Init[⇐$] : Pred[⇐$]² EvInit
Init[⇐$] = [⇐]→₁[⇐$] Init[⇐]

uid[⇒] : Pred[⇒]² (HasUid uid)
uid[⇒] = [$⇒]→₁[⇒] uid[$⇒]

uid[⇐$] : Pred[⇐$]² (HasUid uid)
uid[⇐$] = [⇐]→₁[⇐$] uid[⇐]

¬uid[⇒] : Pred[⇒]² (¬₁ HasUid uid)
¬uid[⇒] = ¬₁[⇒] uid[⇐$]

¬uid[⇐$] : Pred[⇐$]² (¬₁ HasUid uid)
¬uid[⇐$] = ¬₁[⇐$] uid[⇒]

¬uid[⇐] : Pred[⇐]² (¬₁ HasUid uid)
¬uid[⇐] = [⇐$]→₁[⇐] ¬uid[⇐$]

tid[⇒] : Pred[⇒]² (HasTid tid)
tid[⇒] = [$⇒]→₁[⇒] tid[$⇒]

tid[⇐$] : Pred[⇐$]² (HasTid tid)
tid[⇐$] = [⇐]→₁[⇐$] tid[⇐]


-- ## Mapping: Relations

-- | Forward mapping of trivially-mapped relations (see `src-rel`)
rel[$⇒] : {R : Rel₀ Eventᵗ}
  → (Rˡ∈dst : ∀ {x y} → R x y → x ∈ events dst)
  → (Rʳ∈dst : ∀ {x y} → R x y → y ∈ events dst)
    -------------------------------------------
  → Rel[$⇒] (src-rel Rˡ∈dst Rʳ∈dst) R
rel[$⇒] {R} Rˡ∈dst Rʳ∈dst x∈dst y∈dst (_ , _ , dst-R[xy] , p , q) =
  subst-rel R
    (ev[$⇒]eq (Rˡ∈dst dst-R[xy]) x∈dst (≡-sym p))
    (ev[$⇒]eq (Rʳ∈dst dst-R[xy]) y∈dst (≡-sym q))
    dst-R[xy]

-- | Backward mapping of trivially-mapped relations (see `src-rel`)
rel[⇐] : {R : Rel₀ Eventᵗ}
  → (Rˡ∈dst : ∀ {x y} → R x y → x ∈ events dst)
  → (Rʳ∈dst : ∀ {x y} → R x y → y ∈ events dst)
    -------------------------------------------
  → Rel[⇐] (src-rel Rˡ∈dst Rʳ∈dst) R
rel[⇐] {R} Rˡ∈dst Rʳ∈dst {x} {y} x∈dst y∈dst R[xy] =
  (x , y , R[xy] , ev[⇐]eq x∈dst (Rˡ∈dst R[xy]) , ev[⇐]eq y∈dst (Rʳ∈dst R[xy]))


rmw[$⇒] : Rel[$⇒] src-rmw (rmw dst)
rmw[$⇒] = rel[$⇒] (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)

rmw[⇒] : Rel[⇒] src-rmw (rmw dst)
rmw[⇒] = [$⇒]→₂[⇒] rmw[$⇒]

rmw[⇐] : Rel[⇐] src-rmw (rmw dst)
rmw[⇐] = rel[⇐] (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)

rmw[⇐$] : Rel[⇐$] src-rmw (rmw dst)
rmw[⇐$] = [⇐]→₂[⇐$] rmw[⇐]


rmwˡ[⇐$] : Pred[⇐$] (dom src-rmw) (dom (rmw dst))
rmwˡ[⇐$] x∈src (y , rmw[xy]) =
  let y∈dst = rmwʳ∈ex dst-wf rmw[xy]
  in ev[⇐] y∈dst , rmw[⇐$] x∈src (events[⇐] y∈dst) rmw[xy]

rmwˡ[⇒] : Pred[⇒] (dom src-rmw) (dom (rmw dst))
rmwˡ[⇒] x∈src (y , rmw[xy]) =
  let y∈src = rmwʳ∈src rmw[xy]
  in ev[⇒] y∈src , rmw[⇒] x∈src y∈src rmw[xy]

rmwʳ[⇒] : Pred[⇒] (codom src-rmw) (codom (rmw dst))
rmwʳ[⇒] x∈src (y , rmw[yx]) =
  let y∈src = rmwˡ∈src rmw[yx]
  in ev[⇒] y∈src , rmw[⇒] y∈src x∈src rmw[yx]

¬rmwˡ[⇒] : Pred[⇒] (¬₁ dom src-rmw) (¬₁ dom (rmw dst))
¬rmwˡ[⇒] = ¬₁[⇒] rmwˡ[⇐$]

¬rmwˡ[⇐$] : Pred[⇐$] (¬₁ dom src-rmw) (¬₁ dom (rmw dst))
¬rmwˡ[⇐$] = ¬₁[⇐$] rmwˡ[⇒]


-- ## Mapping: Derived Predicates

¬Init[⇒] : Pred[⇒]² (¬₁ EvInit)
¬Init[⇒] = contraposition ∘ Init[⇐$]

¬Init[⇐$] : Pred[⇐$]² (¬₁ EvInit)
¬Init[⇐$] = contraposition ∘ Init[⇒]

suid[⇒] : Rel[⇒]² SameUid
suid[⇒] x∈src y∈src (same-uid x-uid y-uid) =
  same-uid (uid[⇒] x∈src x-uid) (uid[⇒] y∈src y-uid)

suid[⇐$] : Rel[⇐$]² SameUid
suid[⇐$] x∈src y∈src (same-uid x-uid y-uid) =
  same-uid (uid[⇐$] x∈src x-uid) (uid[⇐$] y∈src y-uid)

stid[⇒] : Rel[⇒]² SameTid
stid[⇒] x∈src y∈src (same-tid x-tid y-tid) =
  same-tid (tid[⇒] x∈src x-tid) (tid[⇒] y∈src y-tid)

stid[⇐$] : Rel[⇐$]² SameTid
stid[⇐$] x∈src y∈src (same-tid x-tid y-tid) =
  same-tid (tid[⇐$] x∈src x-tid) (tid[⇐$] y∈src y-tid)

init/tid[⇒] : ∀ {tid : ThreadId} → Pred[⇒]² (EvInit ∪₁ HasTid tid)
init/tid[⇒] x∈src (inj₁ x-init) = inj₁ (Init[⇒] x∈src x-init)
init/tid[⇒] x∈src (inj₂ x-tid)  = inj₂ (tid[⇒] x∈src x-tid)

init+e/stid[⇐$] : Rel[⇐$]² ( ( EvInit ×₂ EvE ) ∪₂ SameTid )
init+e/stid[⇐$] {_} {y} x∈src y∈src (inj₁ (x-init , _)) = inj₁ (Init[⇐$] x∈src x-init , ev-e y)
init+e/stid[⇐$] {_} {_} x∈src y∈src (inj₂ xy-stid)      = inj₂ (stid[⇐$] x∈src y∈src xy-stid)


-- # WellFormed Fields

src-unique-ids : (uid : UniqueId) → Unique₁ _≡_ (HasUid uid ∩₁ src-events)
src-unique-ids uid (x-uid , x∈src) (y-uid , y∈src) =
  ev[⇐$]eq x∈src y∈src
    (unique-ids uid
      (uid[⇒] x∈src x-uid , events[⇒] x∈src)
      (uid[⇒] y∈src y-uid , events[⇒] y∈src))

src-events-unique : UniquePred src-events
src-events-unique _ (x₁ , x₁∈dst , refl) ( x₂ ,  x₂∈dst , p) with ev[$⇒]eq x₁∈dst x₂∈dst p
src-events-unique _ (x₁ , x₁∈dst , refl) ( x₂ ,  x₂∈dst , _)    | refl with events-unique _ x₁∈dst x₂∈dst
src-events-unique _ (x₁ , x₁∈dst , refl) (.x₁ , .x₁∈dst , refl) | refl | refl = refl

src-events-uid-dec : (uid : UniqueId) → Dec (∃[ x ] (HasUid uid ∩₁ src-events) x)
src-events-uid-dec uid with events-uid-dec uid
src-events-uid-dec uid | yes (y , y-uid , y∈dst) = yes (ev[⇐] y∈dst , uid[⇐] y∈dst y-uid , events[⇐] y∈dst)
src-events-uid-dec uid | no  ¬∃x = no lemma
  where
  lemma : ¬ (∃[ x ] (HasUid uid ∩₁ src-events) x)
  lemma (x , x-uid , x∈src) = ¬∃x (ev[⇒] x∈src , uid[⇒] x∈src x-uid , events[⇒] x∈src)

-- Helper. Copied from DerivedWellformed. Used by `src-rmwˡ-xm`
src-events-dec : DecPred src-events
src-events-dec x with src-events-uid-dec (ev-uid x)
src-events-dec x | yes (y , y-uid-x , y∈src) with ev-dec≡ x y
src-events-dec x | yes (.x , y-uid-x , y∈src) | yes refl = yes y∈src
src-events-dec x | yes (y , y-uid-x , y∈src)  | no x≢y  =
  no λ{x∈src → x≢y (src-unique-ids (ev-uid x) (ev-has-uid x , x∈src) (y-uid-x , y∈src))}
src-events-dec x | no ¬∃x = no (λ{x∈src → ¬∃x (x , ev-has-uid x , x∈src)})

src-rmwˡ-dec : DecPred (dom (src-rmw))
src-rmwˡ-dec x with src-events-dec x
... | no x∉src = no (λ{(y , rmw[xy]) → x∉src (rmwˡ∈src rmw[xy])})
... | yes x∈src with rmwˡ-dec (ev[⇒] x∈src)
... | yes (y , rmw[xy]) =
        let y∈dst = rmwʳ∈ex dst-wf rmw[xy]
        in yes (ev[⇐] y∈dst , rmw[⇐$] x∈src (events[⇐] y∈dst) rmw[xy])
... | no x∉rmwˡ = no (¬rmwˡ[⇐$] x∈src x∉rmwˡ)


-- #

starˡ∈src : {x y : Eventˢ}
  → Rˢ ˡ∈src
  → y ∈ src-events
  → Star Rˢ x y
    --------------
  → x ∈ src-events
starˡ∈src Rˡ∈src y∈src R*xy = *-predˡ (λ{_ → Rˡ∈src}) R*xy y∈src

starʳ∈src : {x y : Eventˢ}
  → Rˢ ʳ∈src
  → x ∈ src-events
  → Star Rˢ x y
    --------------
  → y ∈ src-events
starʳ∈src Rʳ∈src x∈src R*xy = *-predʳ (λ{_ → Rʳ∈src}) R*xy x∈src

star[⇒]ˡ :
    Rˢ ˡ∈src
  → Rel[⇒] Rˢ Rᵗ
    --------------------------
  → Rel[⇒] (Star Rˢ) (Star Rᵗ)
star[⇒]ˡ {Rₛ} {Rₜ} Rₛˡ∈src R[⇒] x∈src y∈src ε =
  let v : ev[⇒] x∈src ≡ ev[⇒] y∈src
      v = Eq.cong ev[⇒] (src-events-unique _ x∈src y∈src)
  in subst-rel (Star Rₜ) refl v ε
star[⇒]ˡ {Rₛ} {Rₜ} Rₛˡ∈src R[⇒] x∈src y∈src (R[xz] ◅ R*[zy]) =
  let z∈src = starˡ∈src Rₛˡ∈src y∈src R*[zy]
  in R[⇒] x∈src z∈src R[xz] ◅ star[⇒]ˡ Rₛˡ∈src R[⇒] z∈src y∈src R*[zy]

star[⇒]ʳ :
    Rˢ ʳ∈src
  → Rel[⇒] Rˢ Rᵗ
    --------------------------
  → Rel[⇒] (Star Rˢ) (Star Rᵗ)
star[⇒]ʳ {Rₛ} {Rₜ} Rₛʳ∈src R[⇒] x∈src y∈src ε =
  let v : ev[⇒] x∈src ≡ ev[⇒] y∈src
      v = Eq.cong ev[⇒] (src-events-unique _ x∈src y∈src)
  in subst-rel (Star Rₜ) refl v ε
star[⇒]ʳ {Rₛ} {Rₜ} Rₛʳ∈src R[⇒] x∈src y∈src (R[xz] ◅ R*[zy]) =
  let z∈src = Rₛʳ∈src R[xz]
  in R[⇒] x∈src z∈src R[xz] ◅ star[⇒]ʳ Rₛʳ∈src R[⇒] z∈src y∈src R*[zy]

refl[⇒] :
    Rel[⇒] Rˢ Rᵗ
    ----------------------------------------
  → Rel[⇒] (ReflClosure Rˢ) (ReflClosure Rᵗ)
refl[⇒] {Rᵗ = Rᵗ} R[⇒] x∈src y∈src refl =
  let v : ev[⇒] x∈src ≡ ev[⇒] y∈src
      v = Eq.cong ev[⇒] (src-events-unique _ x∈src y∈src)
  in subst-rel (ReflClosure Rᵗ) refl v refl
refl[⇒] R[⇒] x∈src y∈src [ R[xy] ] = [ R[⇒] x∈src y∈src R[xy] ]
