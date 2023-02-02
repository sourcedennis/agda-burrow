{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.Framework.Mapping.Core using (MappingFramework)

-- | Some basic definitions derived from `MappingFramework`.
module Burrow.Framework.Mapping.Definitions
  {archˢ : Arch}
  {archᵗ : Arch}
  {dst : Execution {archᵗ}}
  {dst-wf : WellFormed dst}
  (δ : MappingFramework archˢ dst-wf)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel)
open import Relation.Binary using (Transitive; Trichotomous; IsStrictTotalOrder; tri<; tri≈; tri>)
open import Relation.Binary using () renaming (IsStrictTotalOrder to STO)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Burrow.Primitives
open import Burrow.Event.Pred
open import Burrow.Event.Rel
open import Burrow.Event.Properties
open import Burrow.Execution.Derived
open import Burrow.WellFormed.Derived dst-wf
open import Burrow.Framework.Definition archˢ dst-wf as Ψ

open MappingFramework δ -- defines ψ
open Ψ.GeneralFramework ψ -- defines ev[⇐]

open import Burrow.Framework.Primitives dst-wf ev[⇐]
open import Burrow.Framework.WellFormed ψ
open Execution


-- # Execution

src : Execution {archˢ}
src =
  record {
    events = src-events
  ; po     = src-rel poˡ∈ex poʳ∈ex
  ; rf     = src-rel rfˡ∈ex rfʳ∈ex
  ; co     = src-rel coˡ∈ex coʳ∈ex
  ; rmw    = src-rmw
  }



-- # Mapping

poˡ∈src : po src ˡ∈src
poˡ∈src = relˡ∈src poˡ∈ex poʳ∈ex

poʳ∈src : po src ʳ∈src
poʳ∈src = relʳ∈src poˡ∈ex poʳ∈ex

udr-po∈src : udr[ po src ]∈src
udr-po∈src = lr→udr (po src) poˡ∈src poʳ∈src


rfˡ∈src : rf src ˡ∈src
rfˡ∈src = relˡ∈src rfˡ∈ex rfʳ∈ex

rfʳ∈src : rf src ʳ∈src
rfʳ∈src = relʳ∈src rfˡ∈ex rfʳ∈ex

udr-rf∈src : udr[ rf src ]∈src
udr-rf∈src = lr→udr (rf src) rfˡ∈src rfʳ∈src


coˡ∈src : co src ˡ∈src
coˡ∈src = relˡ∈src coˡ∈ex coʳ∈ex

coʳ∈src : co src ʳ∈src
coʳ∈src = relʳ∈src coˡ∈ex coʳ∈ex

udr-co∈src : udr[ co src ]∈src
udr-co∈src = lr→udr (co src) coˡ∈src coʳ∈src


frˡ∈src : fr src ˡ∈src
frˡ∈src (rf⁻¹[xz] ⨾[ z ]⨾ co[zy]) = rfʳ∈src rf⁻¹[xz]

frʳ∈src : fr src ʳ∈src
frʳ∈src (rf⁻¹[xz] ⨾[ z ]⨾ co[zy]) = coʳ∈src co[zy]

udr-fr∈src : udr[ fr src ]∈src
udr-fr∈src = lr→udr (fr src) frˡ∈src frʳ∈src


-- # Mapping

-- ## Mapping: Predicates

loc[⇒] : ∀ {loc : Location} → Pred[⇒]² (HasLoc loc)
loc[⇒]  = [$⇒]→₁[⇒] loc[$⇒]

loc[⇐$] : ∀ {loc : Location} → Pred[⇐$]² (HasLoc loc)
loc[⇐$] = [⇐]→₁[⇐$] loc[⇐]


val[⇒] : ∀ {val : Value} → Pred[⇒]² (HasVal val)
val[⇒]  = [$⇒]→₁[⇒] val[$⇒]

val[⇐$] : ∀ {val : Value} → Pred[⇐$]² (HasVal val)
val[⇐$] = [⇐]→₁[⇐$] val[⇐]


-- ## Mapping: Derived Predicates

sloc[⇒] : Rel[⇒]² SameLoc
sloc[⇒] x∈src y∈src (same-loc x-loc y-loc) =
  same-loc (loc[⇒] x∈src x-loc) (loc[⇒] y∈src y-loc)

sloc[⇐$] : Rel[⇐$]² SameLoc
sloc[⇐$] x∈src y∈src (same-loc x-loc y-loc) =
  same-loc (loc[⇐$] x∈src x-loc) (loc[⇐$] y∈src y-loc)

sval[⇒] : Rel[⇒]² SameVal
sval[⇒] x∈src y∈src (same-val x-val y-val) =
  same-val (val[⇒] x∈src x-val) (val[⇒] y∈src y-val)

sval[⇐$] : Rel[⇐$]² SameVal
sval[⇐$] x∈src y∈src (same-val x-val y-val) =
  same-val (val[⇐$] x∈src x-val) (val[⇐$] y∈src y-val)


Wₜ[⇒] : {tag : Tag} → Pred[⇒]² (EvWₜ tag)
Wₜ[⇒] {tag} x∈src = Wₜ[$⇒] (events[⇒] x∈src) ∘ (subst (EvWₜ tag) (ev[⇒⇐] x∈src))

Wₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvWₜ tag)
Wₜ[⇐$] {tag} x∈src = subst (EvWₜ tag) (≡-sym (ev[⇒⇐] x∈src)) ∘ Wₜ[⇐] (events[⇒] x∈src)


W[⇐$] : Pred[⇐$]² EvW
W[⇐$] x∈src = wₜ⇒w ∘ Wₜ[⇐$] x∈src ∘ w⇒wₜ

W[⇒] : Pred[⇒]² EvW
W[⇒] x∈src = wₜ⇒w ∘ Wₜ[⇒] x∈src ∘ w⇒wₜ

W[⇐] : Pred[⇐]² EvW
W[⇐] x∈dst = wₜ⇒w ∘ Wₜ[⇐] x∈dst ∘ w⇒wₜ


Rₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvRₜ tag)
Rₜ[⇐$] {tag} x∈src = subst (EvRₜ tag) (≡-sym (ev[⇒⇐] x∈src)) ∘ Rₜ[⇐] (events[⇒] x∈src)

Rₜ[⇒] : {tag : Tag} → Pred[⇒]² (EvRₜ tag)
Rₜ[⇒] {tag} x∈src = Rₜ[$⇒] (events[⇒] x∈src) ∘ (subst (EvRₜ tag) (ev[⇒⇐] x∈src))

R[⇐$] : Pred[⇐$]² EvR
R[⇐$] x∈src = rₜ⇒r ∘ Rₜ[⇐$] x∈src ∘ r⇒rₜ

R[⇒] : Pred[⇒]² EvR
R[⇒] x∈src = rₜ⇒r ∘ Rₜ[⇒] x∈src ∘ r⇒rₜ


RW[⇒] : Pred[⇒]² EvRW
RW[⇒] x∈src x-rw with rw/rw x-rw
RW[⇒] x∈src x-rw | inj₁ x-r = r⇒rw (R[⇒] x∈src x-r)
RW[⇒] x∈src x-rw | inj₂ x-w = w⇒rw (W[⇒] x∈src x-w)


-- ## Mapping: Relations

po[⇐] : Rel[⇐] (po src) (po dst)
po[⇐] = rel[⇐] poˡ∈ex poʳ∈ex

po[$⇒] : Rel[$⇒] (po src) (po dst)
po[$⇒] = rel[$⇒] poˡ∈ex poʳ∈ex

po[⇐$] : Rel[⇐$] (po src) (po dst)
po[⇐$] = [⇐]→₂[⇐$] po[⇐]

po[⇒] : Rel[⇒] (po src) (po dst)
po[⇒] = [$⇒]→₂[⇒] po[$⇒]


¬po[⇒] : Rel[⇒] (¬₂ po src) (¬₂ po dst)
¬po[⇒] = ¬₂[⇒] po[⇐$]

po-loc[⇒] : Rel[⇒] (po-loc src) (po-loc dst)
po-loc[⇒] = ∩₂[⇒] po[⇒] sloc[⇒]

po⁺[⇒] : Rel[⇒] (TransClosure (po src)) (TransClosure (po dst))
po⁺[⇒] = ⁺[⇒]ˡ poˡ∈src po[⇒]

udr-po[⇐] : Pred[⇐] (udr (po src)) (udr (po dst))
udr-po[⇐] = udr[⇐] (po src) (po dst) po∈ex po[⇐]

udr-po[⇐$] : Pred[⇐$] (udr (po src)) (udr (po dst))
udr-po[⇐$] = [⇐]→₁[⇐$] udr-po[⇐]


po⁺[⇐] : Rel[⇐] (TransClosure (po src)) (TransClosure (po dst))
po⁺[⇐] = ⁺[⇐]ˡ poˡ∈ex po[⇐]

pi[$⇒] : Rel[$⇒] (po-imm src) (po-imm dst)
pi[$⇒] = imm[$⇒]ˡ poˡ∈ex po[⇐] po[$⇒]

pi[⇒] : Rel[⇒] (po-imm src) (po-imm dst)
pi[⇒] = [$⇒]→₂[⇒] pi[$⇒]

pi[⇐$] : Rel[⇐$] (po-imm src) (po-imm dst)
pi[⇐$] = imm[⇐$]ˡ poˡ∈src po[⇒] po[⇐$]

pi[⇐] : Rel[⇐] (po-imm src) (po-imm dst)
pi[⇐] = [⇐$]→₂[⇐] pi[⇐$]

pi⁺[⇒] : Rel[⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[⇒] = ⁺[⇒]ˡ (poˡ∈src ∘ proj₁) pi[⇒]

pi⁺[$⇒] : Rel[$⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[$⇒] = [⇒]→₂[$⇒] pi⁺[⇒]

pi⁺[⇐] : Rel[⇐] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[⇐] = ⁺[⇐]ˡ (poˡ∈ex ∘ proj₁) pi[⇐]

pi⁺[⇐$] : Rel[⇐$] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
pi⁺[⇐$] = [⇐]→₂[⇐$] pi⁺[⇐]


rf[$⇒] : Rel[$⇒] (rf src) (rf dst)
rf[$⇒] = rel[$⇒] rfˡ∈ex rfʳ∈ex

rf[⇒] : Rel[⇒] (rf src) (rf dst)
rf[⇒] = [$⇒]→₂[⇒] rf[$⇒]

rf[⇐] : Rel[⇐] (rf src) (rf dst)
rf[⇐] = rel[⇐] rfˡ∈ex rfʳ∈ex

rf[⇐$] : Rel[⇐$] (rf src) (rf dst)
rf[⇐$] = [⇐]→₂[⇐$] rf[⇐]

rfe[⇒] : Rel[⇒] (rfe src) (rfe dst)
rfe[⇒] = ∩₂[⇒] rf[⇒] ¬po[⇒]


co[$⇒] : Rel[$⇒] (co src) (co dst)
co[$⇒] = rel[$⇒] coˡ∈ex coʳ∈ex

co[⇒] : Rel[⇒] (co src) (co dst)
co[⇒] = [$⇒]→₂[⇒] co[$⇒]

co[⇐] : Rel[⇐] (co src) (co dst)
co[⇐] = rel[⇐] coˡ∈ex coʳ∈ex

co[⇐$] : Rel[⇐$] (co src) (co dst)
co[⇐$] = [⇐]→₂[⇐$] co[⇐]

coe[⇒] : Rel[⇒] (coe src) (coe dst)
coe[⇒] = ∩₂[⇒] co[⇒] ¬po[⇒]


fr[⇒] : Rel[⇒] (fr src) (fr dst)
fr[⇒] x∈src y∈src (rf⁻¹[xz] ⨾[ z ]⨾ co[zy]) =
  let z∈src = coˡ∈src co[zy]
  in rf[⇒] z∈src x∈src rf⁻¹[xz] ⨾[ ev[⇒] z∈src ]⨾ co[⇒] z∈src y∈src co[zy]

fre[⇒] : Rel[⇒] (fre src) (fre dst)
fre[⇒] = ∩₂[⇒] fr[⇒] ¬po[⇒]
