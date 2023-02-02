{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.Framework.Elimination using (EliminationFramework)

module Burrow.Framework.Elimination.WellFormed
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
open import Relation.Binary using (Transitive; Trichotomous; IsStrictTotalOrder; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
-- Library imports
open import Dodo.Unary
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
open import Burrow.Framework.Elimination.Definitions δ
open Execution
open WellFormed


src-rmw-def : src-rmw ⊆₂ immediate (po src)
src-rmw-def = ⊆: lemma
  where
  lemma : src-rmw ⊆₂' immediate (po src)
  lemma x y rmw[xy] = 
    let x∈src = rmwˡ∈src rmw[xy]
        y∈src = rmwʳ∈src rmw[xy]
        dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        dst-pi[xy] = ⊆₂-apply (rmw-def dst-wf) dst-rmw[xy]
    in pi[⇐$] x∈src y∈src dst-pi[xy]


src-rmw-w : codom (src-rmw) ⇔₁ (src-events ∩₁ EvWₜ trmw)
src-rmw-w = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : codom (src-rmw) ⊆₁' (src-events ∩₁ EvWₜ trmw)
  ⊆-proof y (x , rmw[xy]) =
    let x∈src = rmwˡ∈src rmw[xy]
        y∈src = rmwʳ∈src rmw[xy]
        dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
        (_ , dst-y-w) = ⇔₁-apply-⊆₁ (rmw-w dst-wf) (ev[⇒] x∈src , dst-rmw[xy])
    in y∈src , Wₜ[⇐$] y∈src dst-y-w

  ⊇-proof : (src-events ∩₁ EvWₜ trmw) ⊆₁' codom (src-rmw)
  ⊇-proof y (y∈src , y-w) =
    let ¬y-elim = λ{refl → disjoint-rwₜ _ (rwₙₜ⇒rwₜ elim-r/w , wₜ⇒rwₜ y-w)}
        (x , dst-rmw[xy]) = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (events[⇒] y∈src , Wₜ[⇒] ¬y-elim y∈src y-w)
        x∈dst = rmwˡ∈ex dst-rmw[xy]
    in ev[⇐] x∈dst , rmw[⇐$] (events[⇐] x∈dst) y∈src dst-rmw[xy]

src-rmw-r×w : src-rmw ⊆₂ EvRₜ trmw ×₂ EvWₜ trmw
src-rmw-r×w = ⊆: lemma
  where
  lemma : src-rmw ⊆₂' EvRₜ trmw ×₂ EvWₜ trmw
  lemma _ _ rmw[xy] = 
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

src-po-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ src-events) (po src))
src-po-tri tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
  with po-tri dst-wf tid (with-pred (ev[⇒] x∈src) (init/tid[⇒] x∈src x-init/tid , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (init/tid[⇒] y∈src y-init/tid , events[⇒] y∈src))
... | tri<  po[xy] x≢y ¬po[yx] = tri< (po[⇐$] x∈src y∈src po[xy])   (λ{refl → x≢y refl}) (¬po[yx] ∘ po[⇒] y∈src x∈src)
... | tri≈ ¬po[xy] x≡y ¬po[yx] = tri≈ (¬po[xy] ∘ po[⇒] x∈src y∈src) lemma (¬po[yx] ∘ po[⇒] y∈src x∈src)
  where
  unique-pred : UniquePred ((EvInit ∪₁ HasTid tid) ∩₁ src-events)
  unique-pred =
    ∩₁-unique-pred (∪₁-unique-pred (λ{_ (ev-init , ())}) init-unique has-tid-unique) src-events-unique
  lemma : with-pred x (x-init/tid , x∈src) ≡ with-pred y (y-init/tid , y∈src)
  lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-init/tid , x∈src) (y-init/tid , y∈src)
... | tri> ¬po[xy] x≢y  po[yx] = tri> (¬po[xy] ∘ po[⇒] x∈src y∈src) (λ{refl → x≢y refl}) (po[⇐$] y∈src x∈src po[yx])


src-po-splittable : SplittableOrder (po src)
src-po-splittable = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : po src ⊆₂' TransClosure (po-imm src)
  ⊆-proof _ _ po[xy] =
    let x∈src = poˡ∈src po[xy]
        y∈src = poʳ∈src po[xy]
        dst-po[xy] = po[⇒] x∈src y∈src po[xy]
        dst-pi⁺[xy] = ⇔₂-apply-⊆₂ (po-splittable dst-wf) dst-po[xy]
    in pi⁺[⇐$] x∈src y∈src dst-pi⁺[xy]

  ⊇-proof : TransClosure (po-imm src) ⊆₂' po src
  ⊇-proof _ _ pi⁺[xy] = 
    let x∈src = ⁺-lift-predˡ (poˡ∈src ∘ proj₁) pi⁺[xy]
        y∈src = ⁺-lift-predʳ (poʳ∈src ∘ proj₁) pi⁺[xy]
        dst-pi⁺[xy] = pi⁺[⇒] x∈src y∈src pi⁺[xy]
        dst-po[xy] = ⇔₂-apply-⊇₂ (po-splittable dst-wf) dst-pi⁺[xy]
    in po[⇐$] x∈src y∈src dst-po[xy]


src-po-elements : udr (po src) ⇔₁ events src
src-po-elements = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : udr (po src) ⊆₁' events src
  ⊆-proof _ = udr-po∈src

  ⊇-proof : src-events ⊆₁' udr (po src)
  ⊇-proof x x∈src = udr-po[⇐$] x∈src (⇔₁-apply-⊇₁ (po-elements dst-wf) (events[⇒] x∈src))


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


src-wf-init-≥1 : (loc : Location) → NonEmpty₁ (EvInit ∩₁ HasLoc loc ∩₁ src-events)
src-wf-init-≥1 loc =
  let (x , x-init , x-loc , x∈dst) = wf-init-≥1 dst-wf loc
      x∈src = events[⇐] x∈dst
  in ev[⇐] x∈dst , Init[⇐$] x∈src x-init , loc[⇐$] x∈src x-loc , x∈src


src-wf-init-≤1 : (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ src-events)
src-wf-init-≤1 loc {x} {y} (x-init , x-loc , x∈src) (y-init , y-loc , y∈src) =
  let ¬x-elim = λ{refl → elim-¬init x-init}
      ¬y-elim = λ{refl → elim-¬init y-init}
      dst-x≡y = wf-init-≤1 dst-wf loc
                  (Init[⇒] x∈src x-init , loc[⇒] ¬x-elim x∈src x-loc , events[⇒] x∈src)
                  (Init[⇒] y∈src y-init , loc[⇒] ¬y-elim y∈src y-loc , events[⇒] y∈src)
  in ev[⇐$]eq x∈src y∈src dst-x≡y
