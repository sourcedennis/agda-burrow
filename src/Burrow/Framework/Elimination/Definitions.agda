{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.Framework.Elimination using (EliminationFramework)

module Burrow.Framework.Elimination.Definitions
  {arch : Arch}
  {dst : Execution {arch}}
  {dst-wf : WellFormed dst}
  (δ : EliminationFramework dst-wf)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym)
open import Function using (_∘_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using ([_,_])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
-- Library imports
open import Dodo.Unary using (Pred₀)
open import Dodo.Binary
-- Local imports
import Burrow.Framework.Definition arch {arch} dst-wf as Ψ
open import Burrow.Execution.Derived
open import Burrow.WellFormed.Derived dst-wf
open import Burrow.Primitives
open import Burrow.Event.Core
open import Burrow.Event.Pred
open import Burrow.Event.Rel
open import Burrow.Event.Properties
open import Burrow.Internal.Helpers


open EliminationFramework δ -- defines ψ
open Ψ.GeneralFramework ψ -- defines ev[⇐]
open import Burrow.Framework.Primitives dst-wf ev[⇐]
open import Burrow.Framework.WellFormed ψ
open Execution
open WellFormed


-- # Execution

src : Execution {arch}
src =
  record {
    events = src-events
  ; po     = src-rel poˡ∈ex poʳ∈ex
  ; rf     = src-rf
  ; co     = src-co
  ; rmw    = src-rmw
  }


-- # Mapping

-- ## Mapping: Helpers

poˡ∈src : po src ˡ∈src
poˡ∈src = relˡ∈src poˡ∈ex poʳ∈ex

poʳ∈src : po src ʳ∈src
poʳ∈src = relʳ∈src poˡ∈ex poʳ∈ex

udr-po∈src : udr[ po src ]∈src
udr-po∈src = lr→udr (po src) poˡ∈src poʳ∈src


-- ## Mapping: General

-- | The eliminated event in the source execution
src-elim-ev : Event
src-elim-ev = ev[⇐] elim∈ex


-- ## Mapping: Equality

-- | If a mapped event is the eliminated (skip) event in the target,
-- then the source event is the eliminated event.
elim[⇐$]eq : {x : Event}
  → (x∈src : x ∈ src-events)
  → ev[⇒] x∈src ≡ elim-ev
    ---------------------
  → x ≡ src-elim-ev
elim[⇐$]eq (_ , elim∈dst , refl) refl = cong ev[⇐] (events-unique dst-wf _ elim∈dst elim∈ex)

-- | If an event in the source is /not/ the eliminated event,
-- its mapped event is not the eliminated (skip) event.
elim[⇒]neq : {x : Event}
  → (x∈src : x ∈ src-events)
  → x ≢ src-elim-ev
    ---------------------
  → ev[⇒] x∈src ≢ elim-ev
elim[⇒]neq = contrapositive ∘ elim[⇐$]eq

elim[⇐]neq : {x : Event}
  → (x∈dst : x ∈ events dst)
  → x ≢ elim-ev
    ---------------------------
  → (ev[⇐] x∈dst) ≢ src-elim-ev
elim[⇐]neq x∈dst = contrapositive (ev[$⇒]eq x∈dst elim∈ex)


-- ## Mapping: Types

-- These definitions are here (instead of in `Burrow.Framework.Elimination`) because they reference
-- `src-elim-ev`.


-- | /Conditional/ forward mapping of predicates.
-- The mapping holds for any event that is /not the eliminated event/.
CPred[⇒] : Rel₀ (Pred₀ Event)
CPred[⇒] Pˢ Pᵗ = ∀ {x}
  → x ≢ src-elim-ev
  → (x∈src : x ∈ events src)
  → Pˢ x
  → Pᵗ (ev[⇒] x∈src)

-- | /Conditional/ forward mapping of relations.
-- The mapping holds for any event that is /not the eliminated event/.
CRel[⇒] : Rel₀ (Rel₀ Event)
CRel[⇒] Rˢ Rᵗ = ∀ {x y}
  → x ≢ src-elim-ev → y ≢ src-elim-ev
  → (x∈src : x ∈ events src) (y∈src : y ∈ events src)
  → Rˢ x y → Rᵗ (ev[⇒] x∈src) (ev[⇒] y∈src)

-- | Conditional forward mapping of a predicate. For every non-eliminated element in the source,
-- the predicate maps to the target.
CPred[⇒]² : Pred₀ (Pred₀ Event)
CPred[⇒]² P = CPred[⇒] P P

-- | Conditional forward mapping of a relation. For every non-eliminated element in the source,
-- the predicate maps to the target.
CRel[⇒]² : Pred₀ (Rel₀ Event)
CRel[⇒]² R = CRel[⇒] R R


-- ## Mapping: Converters

-- Similar to `[$⇒]→₁[⇒]`, but defined over `CPred[⇒]` instead of `Pred[⇒]`
[$⇒]→₁[⇒]ᶜ :
    {Pˢ : Pred₀ Event}
  → {Pᵗ : Pred₀ Event}
  → CPred[$⇒] Pˢ Pᵗ
    ---------------
  → CPred[⇒] Pˢ Pᵗ
[$⇒]→₁[⇒]ᶜ {Pˢ} P[$⇒] ¬x-elim x∈src =
  P[$⇒] (elim[⇒]neq x∈src ¬x-elim) (events[⇒] x∈src) ∘ subst Pˢ (ev[⇒⇐] x∈src)

-- Similar to `[$⇒]→₂[⇒]`, but defined over `CRel[⇒]` instead of `Rel[⇒]`
[$⇒]→₂[⇒]ᶜ :
    {Rˢ : Rel₀ Event}
  → {Rᵗ : Rel₀ Event}
  → CRel[$⇒] Rˢ Rᵗ
    ---------------
  → CRel[⇒] Rˢ Rᵗ
[$⇒]→₂[⇒]ᶜ {Rˢ} {Rᵗ} R[$⇒] ¬x-elim ¬y-elim x∈src y∈src =
  R[$⇒]
    (elim[⇒]neq x∈src ¬x-elim) (elim[⇒]neq y∈src ¬y-elim)
    (events[⇒] x∈src) (events[⇒] y∈src)
  ∘ Eq.subst₂ Rˢ (ev[⇒⇐] x∈src) (ev[⇒⇐] y∈src)


-- ## Mapping: Predicates

loc[⇒] : {loc : Location} → CPred[⇒]² (HasLoc loc)
loc[⇒] = [$⇒]→₁[⇒]ᶜ loc[$⇒]

loc[⇐$] : {loc : Location} → Pred[⇐$]² (HasLoc loc)
loc[⇐$] = [⇐]→₁[⇐$] loc[⇐]

val[⇒] : {val : Value} → CPred[⇒]² (HasVal val)
val[⇒] = [$⇒]→₁[⇒]ᶜ val[$⇒]

val[⇐$] : {val : Value} → Pred[⇐$]² (HasVal val)
val[⇐$] = [⇐]→₁[⇐$] val[⇐]


sloc[⇒] : CRel[⇒]² SameLoc
sloc[⇒] ¬x-elim ¬y-elim x∈src y∈src (same-loc x-loc y-loc) =
  same-loc (loc[⇒] ¬x-elim x∈src x-loc) (loc[⇒] ¬y-elim y∈src y-loc)

sloc[⇐$] : Rel[⇐$]² SameLoc
sloc[⇐$] x∈src y∈src (same-loc x-loc y-loc) =
  same-loc (loc[⇐$] x∈src x-loc) (loc[⇐$] y∈src y-loc)

sval[⇐$] : Rel[⇐$]² SameVal
sval[⇐$] x∈src y∈src (same-val x-val y-val) =
  same-val (val[⇐$] x∈src x-val) (val[⇐$] y∈src y-val)


Wₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvWₜ tag)
Wₜ[⇐$] = [⇐]→₁[⇐$] Wₜ[⇐]

Wₜ[$⇒] : {tag : Tag} → CPred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {tmov} ¬x-elim = Wᵣ[$⇒] ¬x-elim
Wₜ[$⇒] {trmw} ¬x-elim = Wₐ[$⇒]

Wₜ[⇒] : {tag : Tag} → CPred[⇒]² (EvWₜ tag)
Wₜ[⇒] = [$⇒]→₁[⇒]ᶜ Wₜ[$⇒]

Wₐ[⇒] : Pred[⇒]² (EvWₜ trmw)
Wₐ[⇒] = [$⇒]→₁[⇒] Wₐ[$⇒]


W[⇐] : Pred[⇐]² EvW
W[⇐] x∈dst = wₜ⇒w ∘ Wₜ[⇐] x∈dst ∘ w⇒wₜ

W[⇐$] : Pred[⇐$]² EvW
W[⇐$] = [⇐]→₁[⇐$] W[⇐]

W[⇒] : CPred[⇒]² EvW
W[⇒] ¬x-elim x∈src = wₜ⇒w ∘ Wₜ[⇒] ¬x-elim x∈src ∘ w⇒wₜ

W[$⇒] : CPred[$⇒]² EvW
W[$⇒] ¬x-elim x∈dst = wₜ⇒w ∘ Wₜ[$⇒] ¬x-elim x∈dst ∘ w⇒wₜ


Rₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvRₜ tag)
Rₜ[⇐$] = [⇐]→₁[⇐$] Rₜ[⇐]

Rₜ[$⇒] : {tag : Tag} → CPred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {tmov} ¬x-elim = Rᵣ[$⇒] ¬x-elim
Rₜ[$⇒] {trmw} ¬x-elim = Rₐ[$⇒]

Rₜ[⇒] : {tag : Tag} → CPred[⇒]² (EvRₜ tag)
Rₜ[⇒] = [$⇒]→₁[⇒]ᶜ Rₜ[$⇒]

Rₐ[⇒] : Pred[⇒]² (EvRₜ trmw)
Rₐ[⇒] = [$⇒]→₁[⇒] Rₐ[$⇒]


R[⇐] : Pred[⇐]² EvR
R[⇐] x∈dst = rₜ⇒r ∘ Rₜ[⇐] x∈dst ∘ r⇒rₜ

R[⇐$] : Pred[⇐$]² EvR
R[⇐$] = [⇐]→₁[⇐$] R[⇐]

R[⇒] : CPred[⇒]² EvR
R[⇒] ¬x-elim x∈src = rₜ⇒r ∘ Rₜ[⇒] ¬x-elim x∈src ∘ r⇒rₜ


RW[⇒] : CPred[⇒]² EvRW
RW[⇒] ¬x-elim x∈src = [ r⇒rw ∘ R[⇒] ¬x-elim x∈src , w⇒rw ∘ W[⇒] ¬x-elim x∈src ] ∘ rw/rw

F₌[⇒] : {mode : Arch.LabF arch} → Pred[⇒] (EvFₜ mode) (EvFₜ mode)
F₌[⇒] = [$⇒]→₁[⇒] F₌[$⇒]


-- ## Mapping: Relations

-- ### Mapping - Relations: po

po[⇐] : Rel[⇐] (po src) (po dst)
po[⇐] = rel[⇐] poˡ∈ex poʳ∈ex

po[⇐$] : Rel[⇐$] (po src) (po dst)
po[⇐$] = [⇐]→₂[⇐$] po[⇐]

po[$⇒] : Rel[$⇒] (po src) (po dst)
po[$⇒] = rel[$⇒] poˡ∈ex poʳ∈ex

po[⇒] : Rel[⇒] (po src) (po dst)
po[⇒] = [$⇒]→₂[⇒] po[$⇒]

¬po[⇒] : Rel[⇒] (¬₂ po src) (¬₂ po dst)
¬po[⇒] = ¬₂[⇒] po[⇐$]

po-loc[⇒] : CRel[⇒] (po src ∩₂ SameLoc) (po dst ∩₂ SameLoc)
po-loc[⇒] ¬x-elim ¬y-elim x∈src y∈src (po[xy] , xy-sloc) =
  po[⇒] x∈src y∈src po[xy] , sloc[⇒] ¬x-elim ¬y-elim x∈src y∈src xy-sloc

udr-po[⇐] : Pred[⇐] (udr (po src)) (udr (po dst))
udr-po[⇐] = udr[⇐] (po src) (po dst) po∈ex po[⇐]

udr-po[⇐$] : Pred[⇐$] (udr (po src)) (udr (po dst))
udr-po[⇐$] = [⇐]→₁[⇐$] udr-po[⇐]


-- ### Mapping - Relations: po⁺

po⁺[⇒] : Rel[⇒] (TransClosure (po src)) (TransClosure (po dst))
po⁺[⇒] = ⁺[⇒]ˡ poˡ∈src po[⇒]

po⁺[⇐] : Rel[⇐] (TransClosure (po src)) (TransClosure (po dst))
po⁺[⇐] = ⁺[⇐]ˡ poˡ∈ex po[⇐]


-- ### Mapping - Relations: pi

pi[$⇒] : Rel[$⇒] (po-imm src) (po-imm dst)
pi[$⇒] = imm[$⇒]ˡ poˡ∈ex po[⇐] po[$⇒]

pi[⇒] : Rel[⇒] (po-imm src) (po-imm dst)
pi[⇒] = [$⇒]→₂[⇒] pi[$⇒]

pi[⇐$] : Rel[⇐$] (po-imm src) (po-imm dst)
pi[⇐$] = imm[⇐$]ˡ poˡ∈src po[⇒] po[⇐$]

pi[⇐] : Rel[⇐] (po-imm src) (po-imm dst)
pi[⇐] = [⇐$]→₂[⇐] pi[⇐$]


-- ### Mapping - Relations: pi⁺

pi⁺[⇒] : Rel[⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[⇒] = ⁺[⇒]ˡ (poˡ∈src ∘ proj₁) pi[⇒]

pi⁺[$⇒] : Rel[$⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[$⇒] = [⇒]→₂[$⇒] pi⁺[⇒]

pi⁺[⇐] : Rel[⇐] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[⇐] = ⁺[⇐]ˡ piˡ∈ex pi[⇐]

pi⁺[⇐$] : Rel[⇐$] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[⇐$] = [⇐]→₂[⇐$] pi⁺[⇐]


co[⇒] : CRel[⇒] (co src) (co dst)
co[⇒] = [$⇒]→₂[⇒]ᶜ co[$⇒]

co[⇐$] : Rel[⇐$] (co src) (co dst)
co[⇐$] = [⇐]→₂[⇐$] co[⇐]

coe[⇒] : CRel[⇒] (coe src) (coe dst)
coe[⇒] ¬x-elim ¬y-elim x∈src y∈src (co[xy] , ¬po[xy]) =
  co[⇒] ¬x-elim ¬y-elim x∈src y∈src co[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]


rf[⇒] : CRel[⇒] (rf src) (rf dst)
rf[⇒] = [$⇒]→₂[⇒]ᶜ rf[$⇒]

rf[⇐$] : Rel[⇐$] (rf src) (rf dst)
rf[⇐$] = [⇐]→₂[⇐$] rf[⇐]

rfe[⇒] : CRel[⇒] (rfe src) (rfe dst)
rfe[⇒] ¬x-elim ¬y-elim x∈src y∈src (co[xy] , ¬po[xy]) =
  rf[⇒] ¬x-elim ¬y-elim x∈src y∈src co[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]

-- `fr[⇒]` cannot be proven generally, as it may go:
-- `rf⁻¹ x src-elim-ev ⨾ co src-elim-ev y`
-- in which it cannot go through the eliminated event in the target


-- # Utils

elim-¬init : ¬ EvInit src-elim-ev
elim-¬init elim-init = disjoint-init/rwₙₜ _ (elim-init , elim-r/w)

elim-¬rₐ : ¬ EvRₜ trmw src-elim-ev
elim-¬rₐ elim-r-rmw = disjoint-rwₜ _ (rwₙₜ⇒rwₜ elim-r/w , rₜ⇒rwₜ elim-r-rmw)

elim-¬wₐ : ¬ EvWₜ trmw src-elim-ev
elim-¬wₐ elim-w-rmw = disjoint-rwₜ _ (rwₙₜ⇒rwₜ elim-r/w , wₜ⇒rwₜ elim-w-rmw)
