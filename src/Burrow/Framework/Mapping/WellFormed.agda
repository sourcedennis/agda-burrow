{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.Framework.Mapping.Core using (MappingFramework)


-- | Derives `WellFormed` (for the source) generically from the `MappingFramework`.
module Burrow.Framework.Mapping.WellFormed
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
open import Burrow.WellFormed.Derived
open import Burrow.Framework.Definition archˢ dst-wf as Ψ
open import Burrow.Framework.Mapping.Definitions δ

open MappingFramework δ -- defines ψ
open Ψ.GeneralFramework ψ -- defines ev[⇐]

open import Burrow.Framework.Primitives dst-wf ev[⇐]
open import Burrow.Framework.WellFormed ψ
open Execution
open WellFormed


src-rmw-def : rmw src ⊆₂ po-imm src
src-rmw-def = ⊆: lemma
  where
  lemma : rmw src ⊆₂' po-imm src
  lemma x y rmw[xy] = 
    let x∈src = rmwˡ∈src rmw[xy]
        y∈src = rmwʳ∈src rmw[xy]
        dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        dst-pi[xy] = ⊆₂-apply (rmw-def dst-wf) dst-rmw[xy]
    in pi[⇐$] x∈src y∈src dst-pi[xy]


src-rmw-w : codom (rmw src) ⇔₁ (events src ∩₁ EvWₜ trmw)
src-rmw-w = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : codom (rmw src) ⊆₁' (events src ∩₁ EvWₜ trmw)
  ⊆-proof y (x , rmw[xy]) =
    let x∈src = rmwˡ∈src rmw[xy]
        y∈src = rmwʳ∈src rmw[xy]
        dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        (_ , dst-y-w) = ⇔₁-apply-⊆₁ (rmw-w dst-wf) (ev[⇒] x∈src , dst-rmw[xy])
    in y∈src , Wₜ[⇐$] y∈src dst-y-w

  ⊇-proof : (events src ∩₁ EvWₜ trmw) ⊆₁' codom (rmw src)
  ⊇-proof y (y∈src , y-w) =
    let (x , dst-rmw[xy]) = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (events[⇒] y∈src , Wₜ[⇒] y∈src y-w)
        x∈dst = rmwˡ∈ex dst-wf dst-rmw[xy]
    in (ev[⇐] x∈dst , rmw[⇐$] (events[⇐] x∈dst) y∈src dst-rmw[xy])


src-rf-w×r : rf src ⊆₂ EvW ×₂ EvR
src-rf-w×r = ⊆: lemma
  where
  lemma : rf src ⊆₂' EvW ×₂ EvR
  lemma x y rf[xy] =
    let x∈src = rfˡ∈src rf[xy]
        y∈src = rfʳ∈src rf[xy]
        dst-rf[xy] = rf[⇒] x∈src y∈src rf[xy]
        (x-w , y-r) = ⊆₂-apply (rf-w×r dst-wf) dst-rf[xy]
    in W[⇐$] x∈src x-w , R[⇐$] y∈src y-r


src-co-w×w : co src ⊆₂ EvW ×₂ EvW
src-co-w×w = ⊆: lemma
  where
  lemma : co src ⊆₂' EvW ×₂ EvW
  lemma x y co[xy] =
    let x∈src = coˡ∈src co[xy]
        y∈src = coʳ∈src co[xy]
        dst-co[xy] = co[⇒] x∈src y∈src co[xy]
        (x-w , y-w) = ⊆₂-apply (co-w×w dst-wf) dst-co[xy]
    in W[⇐$] x∈src x-w , W[⇐$] y∈src y-w


src-rmw-r×w : rmw src ⊆₂ EvRₜ trmw ×₂ EvWₜ trmw
src-rmw-r×w = ⊆: lemma
  where
  lemma : rmw src ⊆₂' EvRₜ trmw ×₂ EvWₜ trmw
  lemma x y rmw[xy] = 
    let x∈src = rmwˡ∈src rmw[xy]
        y∈src = rmwʳ∈src rmw[xy]
        dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        (x-r , y-w) = ⊆₂-apply (rmw-r×w dst-wf) dst-rmw[xy]
    in Rₜ[⇐$] x∈src x-r , Wₜ[⇐$] y∈src y-w


src-po-init-first : ⊤-Precedes-⊥ EvInit (po src)
src-po-init-first po[xy] y-init =
  let x∈src = poˡ∈src po[xy]
      y∈src = poʳ∈src po[xy]
      dst-po[xy] = po[⇒] x∈src y∈src po[xy]
      dst-y-init = Init[⇒] y∈src y-init
      dst-x-init = po-init-first dst-wf dst-po[xy] dst-y-init
  in Init[⇐$] x∈src dst-x-init


src-co-init-first : ⊤-Precedes-⊥ EvInit (co src)
src-co-init-first co[xy] y-init =
  let x∈src = coˡ∈src co[xy]
      y∈src = coʳ∈src co[xy]
      dst-co[xy] = co[⇒] x∈src y∈src co[xy]
      dst-y-init = Init[⇒] y∈src y-init
      dst-x-init = co-init-first dst-wf dst-co[xy] dst-y-init
  in Init[⇐$] x∈src dst-x-init


src-po-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events src) (po src))
src-po-tri tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
  with po-tri dst-wf tid (with-pred (ev[⇒] x∈src) (init/tid[⇒] x∈src x-init/tid , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (init/tid[⇒] y∈src y-init/tid , events[⇒] y∈src))
... | tri<  po[xy] x≢y ¬po[yx] = tri< (po[⇐$] x∈src y∈src po[xy])   (λ{refl → x≢y refl}) (¬po[yx] ∘ po[⇒] y∈src x∈src)
... | tri≈ ¬po[xy] x≡y ¬po[yx] = tri≈ (¬po[xy] ∘ po[⇒] x∈src y∈src) lemma (¬po[yx] ∘ po[⇒] y∈src x∈src)
  where
  unique-pred : UniquePred ((EvInit ∪₁ HasTid tid) ∩₁ events src)
  unique-pred =
    ∩₁-unique-pred (∪₁-unique-pred (λ{_ (ev-init , ())}) init-unique has-tid-unique) src-events-unique
  lemma : with-pred x (x-init/tid , x∈src) ≡ with-pred y (y-init/tid , y∈src)
  lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-init/tid , x∈src) (y-init/tid , y∈src)
... | tri> ¬po[xy] x≢y  po[yx] = tri> (¬po[xy] ∘ po[⇒] x∈src y∈src) (λ{refl → x≢y refl}) (po[⇐$] y∈src x∈src po[yx])


src-co-tri : (loc : Location) → Trichotomous _≡_ (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events src) (co src))
src-co-tri loc (with-pred x (x-w , x-loc , x∈src)) (with-pred y (y-w , y-loc , y∈src))
  with co-tri dst-wf loc (with-pred (ev[⇒] x∈src) (W[⇒] x∈src x-w , loc[⇒] x∈src x-loc , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (W[⇒] y∈src y-w , loc[⇒] y∈src y-loc , events[⇒] y∈src))
... | tri<  co[xy] x≢y ¬co[yx] = tri< (co[⇐$] x∈src y∈src co[xy]) (λ{refl → x≢y refl}) (¬co[yx] ∘ co[⇒] y∈src x∈src)
... | tri≈ ¬co[xy] x≡y ¬co[yx] = tri≈ (¬co[xy] ∘ co[⇒] x∈src y∈src) lemma (¬co[yx] ∘ co[⇒] y∈src x∈src)
  where
  unique-pred : UniquePred (EvW ∩₁ HasLoc loc ∩₁ events src)
  unique-pred = ∩₁-unique-pred w-unique (∩₁-unique-pred has-loc-unique src-events-unique)
  lemma : with-pred x (x-w , x-loc , x∈src) ≡ with-pred y (y-w , y-loc , y∈src)
  lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-w , x-loc , x∈src) (y-w , y-loc , y∈src)
... | tri> ¬co[xy] x≢y  co[yx] = tri> (¬co[xy] ∘ co[⇒] x∈src y∈src) (λ{refl → x≢y refl}) (co[⇐$] y∈src x∈src co[yx])


src-po-splittable : SplittableOrder (po src)
src-po-splittable = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : po src ⊆₂' TransClosure (po-imm src)
  ⊆-proof x y po[xy] =
    let x∈src = poˡ∈src po[xy]
        y∈src = poʳ∈src po[xy]
        dst-po[xy] = po[⇒] x∈src y∈src po[xy]
        dst-pi⁺[xy] = ⇔₂-apply-⊆₂ (po-splittable dst-wf) dst-po[xy]
    in pi⁺[⇐$] x∈src y∈src dst-pi⁺[xy]

  ⊇-proof : TransClosure (po-imm src) ⊆₂' po src
  ⊇-proof x y pi⁺[xy] = 
    let x∈src = ⁺-lift-predˡ (poˡ∈src ∘ proj₁) pi⁺[xy]
        y∈src = ⁺-lift-predʳ (poʳ∈src ∘ proj₁) pi⁺[xy]
        dst-pi⁺[xy] = pi⁺[⇒] x∈src y∈src pi⁺[xy]
        dst-po[xy] = ⇔₂-apply-⊇₂ (po-splittable dst-wf) dst-pi⁺[xy]
    in po[⇐$] x∈src y∈src dst-po[xy]


src-co-trans : Transitive (co src)
src-co-trans co[xy] co[yz] =
  let x∈src = coˡ∈src co[xy]
      y∈src = coʳ∈src co[xy]
      z∈src = coʳ∈src co[yz]
      dst-co[xy] = co[⇒] x∈src y∈src co[xy]
      dst-co[yz] = co[⇒] y∈src z∈src co[yz]
      dst-co[xz] = co-trans dst-wf dst-co[xy] dst-co[yz]
  in co[⇐$] x∈src z∈src dst-co[xz]


src-po-elements : udr (po src) ⇔₁ events src
src-po-elements = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : udr (po src) ⊆₁' events src
  ⊆-proof _ = udr-po∈src

  ⊇-proof : events src ⊆₁' udr (po src)
  ⊇-proof x x∈src = udr-po[⇐$] x∈src (⇔₁-apply-⊇₁ (po-elements dst-wf) (events[⇒] x∈src))


src-rf-elements : udr (rf src) ⊆₁ events src
src-rf-elements = ⊆: (λ _ → udr-rf∈src)


src-co-elements : udr (co src) ⊆₁ events src
src-co-elements = ⊆: (λ _ → udr-co∈src)


src-po-stid : po src ⊆₂ ( EvInit ×₂ EvE ) ∪₂ SameTid
src-po-stid = ⊆: lemma
  where
  lemma : po src ⊆₂' ( EvInit ×₂ EvE ) ∪₂ SameTid
  lemma x y po[xy] =
    let x∈src = poˡ∈src po[xy]
        y∈src = poʳ∈src po[xy]
        dst-po[xy] = po[⇒] x∈src y∈src po[xy]
        xy-init+e/stid = ⊆₂-apply (po-stid dst-wf) dst-po[xy]
    in init+e/stid[⇐$] x∈src y∈src xy-init+e/stid


src-rf-sloc : rf src ⊆₂ SameLoc
src-rf-sloc = ⊆: lemma
  where
  lemma : rf src ⊆₂' SameLoc
  lemma x y rf[xy] =
    let x∈src = rfˡ∈src rf[xy]
        y∈src = rfʳ∈src rf[xy]
        dst-rf[xy] = rf[⇒] x∈src y∈src rf[xy]
        xy-sloc = ⊆₂-apply (rf-sloc dst-wf) dst-rf[xy]
    in sloc[⇐$] x∈src y∈src xy-sloc


src-co-sloc : co src ⊆₂ SameLoc
src-co-sloc = ⊆: lemma
  where
  lemma : co src ⊆₂' SameLoc
  lemma x y co[xy] =
    let x∈src = coˡ∈src co[xy]
        y∈src = coʳ∈src co[xy]
        dst-co[xy] = co[⇒] x∈src y∈src co[xy]
        xy-sloc = ⊆₂-apply (co-sloc dst-wf) dst-co[xy]
    in sloc[⇐$] x∈src y∈src xy-sloc


src-rmw-sloc : rmw src ⊆₂ SameLoc
src-rmw-sloc = ⊆: lemma
  where
  lemma : rmw src ⊆₂' SameLoc
  lemma x y rmw[xy] =
    let x∈src = rmwˡ∈src rmw[xy]
        y∈src = rmwʳ∈src rmw[xy]
        dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        xy-sloc = ⊆₂-apply (rmw-sloc dst-wf) dst-rmw[xy]
    in sloc[⇐$] x∈src y∈src xy-sloc


src-rf-sval : rf src ⊆₂ SameVal
src-rf-sval = ⊆: lemma
  where
  lemma : rf src ⊆₂' SameVal
  lemma x y rf[xy] =
    let x∈src = rfˡ∈src rf[xy]
        y∈src = rfʳ∈src rf[xy]
        dst-rf[xy] = rf[⇒] x∈src y∈src rf[xy]
        xy-sval = ⊆₂-apply (rf-sval dst-wf) dst-rf[xy]
    in sval[⇐$] x∈src y∈src xy-sval


src-wf-rf-≥1 : (EvR ∩₁ events src) ⊆₁ codom (rf src)
src-wf-rf-≥1 = ⊆: lemma
  where
  lemma : (EvR ∩₁ events src) ⊆₁' codom (rf src)
  lemma x (x-r , x∈src) =
    let x∈dst = events[⇒] x∈src
        (y , rf[yx]) = ⊆₁-apply (wf-rf-≥1 dst-wf) (R[⇒] x∈src x-r , x∈dst)
        y∈dst = rfˡ∈ex dst-wf rf[yx]
    in take-codom (rf src) (rf[⇐$] (events[⇐] y∈dst) x∈src rf[yx])


src-wf-rf-≤1 : Functional _≡_ (flip (rf src))
src-wf-rf-≤1 x y₁ y₂ rf[y₁x] rf[y₂x] =
  let x∈src = rfʳ∈src rf[y₁x]
      y₁∈src = rfˡ∈src rf[y₁x]
      y₂∈src = rfˡ∈src rf[y₂x]
      dst-rf[y₁x] = rf[⇒] y₁∈src x∈src rf[y₁x]
      dst-rf[y₂x] = rf[⇒] y₂∈src x∈src rf[y₂x]
      dst-y₁≡y₂ = wf-rf-≤1 dst-wf (ev[⇒] x∈src) (ev[⇒] y₁∈src) (ev[⇒] y₂∈src) dst-rf[y₁x] dst-rf[y₂x]
  in ev[⇐$]eq y₁∈src y₂∈src dst-y₁≡y₂


src-wf-init-≥1 : (loc : Location) → NonEmpty₁ (EvInit ∩₁ HasLoc loc ∩₁ events src)
src-wf-init-≥1 loc =
  let (x , x-init , x-loc , x∈dst) = wf-init-≥1 dst-wf loc
      x∈src = events[⇐] x∈dst
  in ev[⇐] x∈dst , Init[⇐$] x∈src x-init , loc[⇐$] x∈src x-loc , x∈src


src-wf-init-≤1 : (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ events src)
src-wf-init-≤1 loc (x-init , x-loc , x∈src) (y-init , y-loc , y∈src) =
  let dst-x≡y = wf-init-≤1 dst-wf loc
                  (Init[⇒] x∈src x-init , loc[⇒] x∈src x-loc , events[⇒] x∈src)
                  (Init[⇒] y∈src y-init , loc[⇒] y∈src y-loc , events[⇒] y∈src)
  in ev[⇐$]eq x∈src y∈src dst-x≡y


src-wf : WellFormed src
src-wf =
  record
    { unique-ids     = src-unique-ids
    ; events-unique  = src-events-unique
    ; rmw-def        = src-rmw-def
    ; rmw-w          = src-rmw-w
    ; rf-w×r         = src-rf-w×r
    ; co-w×w         = src-co-w×w
    ; rmw-r×w        = src-rmw-r×w
    ; po-init-first  = src-po-init-first
    ; co-init-first  = src-co-init-first
    ; po-tri         = src-po-tri
    ; co-tri         = src-co-tri
    ; po-splittable  = src-po-splittable
    ; co-trans       = src-co-trans
    ; events-uid-dec = src-events-uid-dec
    ; rmwˡ-dec       = src-rmwˡ-dec
    ; po-elements    = src-po-elements
    ; rf-elements    = src-rf-elements
    ; co-elements    = src-co-elements
    ; po-stid        = src-po-stid
    ; rf-sloc        = src-rf-sloc
    ; co-sloc        = src-co-sloc
    ; rmw-sloc       = src-rmw-sloc
    ; rf-sval        = src-rf-sval
    ; wf-rf-≥1       = src-wf-rf-≥1
    ; wf-rf-≤1       = src-wf-rf-≤1
    ; wf-init-≥1     = src-wf-init-≥1
    ; wf-init-≤1     = src-wf-init-≤1
    }
