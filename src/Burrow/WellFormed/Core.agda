{-# OPTIONS --safe #-}

open import Burrow.Primitives
open import Burrow.Execution.Core using (Execution)

module Burrow.WellFormed.Core
  {arch : Arch}
  (ex : Execution {arch})
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


-- # Definitions: Well-formedness

record WellFormed : Set where
  field
    -- # General constraints

    unique-ids : ∀ (uid : UniqueId) → Unique₁ _≡_ (HasUid uid ∩₁ events)

    events-unique : UniquePred events

    rmw-def  : rmw ⊆₂ po-imm
    rmw-w    : codom rmw ⇔₁ ( events ∩₁ EvWₜ trmw )

    rf-w×r  : rf  ⊆₂ ( EvW ×₂ EvR )
    co-w×w  : co  ⊆₂ ( EvW ×₂ EvW )
    rmw-r×w : rmw ⊆₂ EvRₜ trmw ×₂ EvWₜ trmw

    -- Note that 'po' and 'co' are /strict/ orders (i.e., irreflexive).
    -- If they were non-strict they'd always be cyclic.
    po-init-first : ⊤-Precedes-⊥ EvInit po -- init events before non-init events
    co-init-first : ⊤-Precedes-⊥ EvInit co -- init events before non-init events

    po-tri : ∀ (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events) po)
    co-tri : ∀ (loc : Location) → Trichotomous _≡_ (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events) co)
    -- between any two non-immediate po-related events, there exists another event
    po-splittable : SplittableOrder po
    co-trans : Transitive co

    -- For every unique ID, either there is an event with that ID, or there is not
    events-uid-dec : (uid : UniqueId) → Dec (∃[ x ] (HasUid uid ∩₁ events) x)
    rmwˡ-dec : DecPred (dom rmw)

    po-elements : udr po ⇔₁ events
    rf-elements : udr rf ⊆₁ events
    co-elements : udr co ⊆₁ events -- this could be: udr co ⇔₁ ( events ∩₁ EvW )

    po-stid  : po  ⊆₂ ((EvInit ×₂ EvE) ∪₂ SameTid)
    rf-sloc  : rf  ⊆₂ SameLoc
    co-sloc  : co  ⊆₂ SameLoc
    rmw-sloc : rmw ⊆₂ SameLoc
    rf-sval  : rf  ⊆₂ SameVal

    -- ## Well formed
    -- Every read-event reads from a preceding write. That is, every read event
    -- shows up in the co-domain of `rf`.
    wf-rf-≥1 : (EvR ∩₁ events) ⊆₁ codom rf
    -- Every read-event reads from *at most* one write
    wf-rf-≤1 : Functional _≡_ (flip rf) -- at most once

    -- All memory locations are initialized
    wf-init-≥1 : ∀ (loc : Location) → NonEmpty₁ (EvInit ∩₁ HasLoc loc ∩₁ events) -- at least once
    wf-init-≤1 : ∀ (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ events) -- at most once


-- ## Well-formedness Properties

behavior : REL₀ Location Value
behavior loc val =
  ∃[ ev ] (ev ∈ events × EvW ev × HasVal val ev × HasLoc loc ev × maximal co ev)
