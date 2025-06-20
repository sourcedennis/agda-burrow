{-# OPTIONS --safe --without-K #-}

open import Burrow.Primitives

module Burrow.Event.Pred {arch : Arch} where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong-app; sym; subst; subst₂)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; Empty)
-- External Library imports
open import Dodo.Unary
open import Dodo.Binary
open import Burrow.Event.Core {arch} using (Event)


open Arch arch
open Event


private
  variable
    uid : UniqueId
    tid : ThreadId
    loc : Location
    val : Value
    lab-r : LabR
    lab-w : LabW
    lab-f : LabF


-- # Unary Predicates

-- | A predicate stating an event has a particular unique identifier.
data HasUid (uid : UniqueId) : Pred₀ Event where
  has-uid-init : HasUid uid (event-init uid loc val)
  has-uid-skip : HasUid uid (event-skip uid tid)
  has-uid-r    : HasUid uid (event-r uid tid loc val lab-r)
  has-uid-w    : HasUid uid (event-w uid tid loc val lab-w)
  has-uid-f    : HasUid uid (event-f uid tid lab-f)

data HasTid (tid : ThreadId) : Pred₀ Event where
  has-tid-skip : HasTid tid (event-skip uid tid)
  has-tid-r    : HasTid tid (event-r uid tid loc val lab-r)
  has-tid-w    : HasTid tid (event-w uid tid loc val lab-w)
  has-tid-f    : HasTid tid (event-f uid tid lab-f)
  
data HasLoc (loc : Location) : Pred₀ Event where
  has-loc-init : HasLoc loc (event-init uid loc val)
  has-loc-r    : HasLoc loc (event-r uid tid loc val lab-r)
  has-loc-w    : HasLoc loc (event-w uid tid loc val lab-w)

data HasVal (val : Value) : Pred₀ Event where
  has-val-init : HasVal val (event-init uid loc val)
  has-val-r    : HasVal val (event-r uid tid loc val lab-r)
  has-val-w    : HasVal val (event-w uid tid loc val lab-w)

data HasTag (tag : Tag) : Pred₀ Event where
  has-tag-init : tag ≡ tmov → HasTag tag (event-init uid loc val)
  has-tag-r    : tag ≡ lab-r-tag lab-r → HasTag tag (event-r uid tid loc val lab-r)
  has-tag-w    : tag ≡ lab-w-tag lab-w → HasTag tag (event-w uid tid loc val lab-w)


-- ## Unary Predicates: Extras

HasSomeUid : Pred₀ Event
HasSomeUid ev = ∃[ uid ] HasUid uid ev

HasSomeTid : Pred₀ Event
HasSomeTid ev = ∃[ tid ] HasTid tid ev

HasSomeLoc : Pred₀ Event
HasSomeLoc ev = ∃[ loc ] HasLoc loc ev

HasSomeVal : Pred₀ Event
HasSomeVal ev = ∃[ val ] HasVal val ev

HasSomeTag : Pred₀ Event
HasSomeTag ev = ∃[ tag ] HasTag tag ev


-- # Event Sets

-- | The set of read events
data EvR : Pred₀ Event where
  ev-r : EvR (event-r uid tid loc val lab-r)

-- | The set of read events indexed by their tag (mov/rmw)
data EvRₜ (tag : Tag) : Pred₀ Event where
  ev-r : tag ≡ lab-r-tag lab-r → EvRₜ tag (event-r uid tid loc val lab-r)

data EvRₗ (lab-r : LabR) : Pred₀ Event where
  ev-r : EvRₗ lab-r (event-r uid tid loc val lab-r)

data EvR₌ (loc : Location) (val : Value) (lab-r : LabR) : Pred₀ Event where
  ev-r : EvR₌ loc val lab-r (event-r uid tid loc val lab-r)

-- | The set of write events
data EvW : Pred₀ Event where
  ev-init : EvW (event-init uid loc val)
  ev-w    : EvW (event-w uid tid loc val lab-w)

-- | The set of write events
data EvWₗ (lab-w : LabW) : Pred₀ Event where
  ev-w : EvWₗ lab-w (event-w uid tid loc val lab-w)

-- | The set of write events indexed by their tag (mov/rmw)
data EvWₜ (tag : Tag) : Pred₀ Event where
  ev-init : tag ≡ tmov → EvWₜ tag (event-init uid loc val)
  ev-w    : tag ≡ lab-w-tag lab-w → EvWₜ tag (event-w uid tid loc val lab-w)

-- | The set of write events, without init events, indexed by their tag (mov/rmw)
data EvWₙₜ (tag : Tag) : Pred₀ Event where
  ev-w : tag ≡ lab-w-tag lab-w → EvWₙₜ tag (event-w uid tid loc val lab-w)

-- | The set of write events, without init events, indexed by their tag (mov/rmw)
data EvWₙ : Pred₀ Event where
  ev-w : EvWₙ (event-w uid tid loc val lab-w)

data EvW₌ (loc : Location) (val : Value) (lab-w : LabW) : Pred₀ Event where
  ev-w : EvW₌ loc val lab-w (event-w uid tid loc val lab-w)
  
-- | The set of fence events
data EvF : Pred₀ Event where
  ev-f : EvF (event-f uid tid lab-f)

data EvF₌ (lab-f : LabF) : Pred₀ Event where
  ev-r : EvF₌ lab-f (event-f uid tid lab-f)

-- | The set of fence events, with the fence label
data EvFₜ (lab-f : LabF) : Pred₀ Event where
  ev-f : EvFₜ lab-f (event-f uid tid lab-f)
  
-- | The set of all events
data EvE : Pred₀ Event where
  ev-init : EvE (event-init uid loc val)
  ev-skip : EvE (event-skip uid tid)
  ev-r    : EvE (event-r uid tid loc val lab-r)
  ev-w    : EvE (event-w uid tid loc val lab-w)
  ev-f    : EvE (event-f uid tid lab-f)

-- | The set of init events
data EvInit : Pred₀ Event where
  ev-init : EvInit (event-init uid loc val)

-- | The set of skip events
data EvSkip : Pred₀ Event where
  ev-skip : EvSkip (event-skip uid tid)

-- | The set of Read/Write events
--
-- # Design decision: Not _∪₁_
--
-- An alternative definition could be:
-- > EvRW = EvR ∪₁ EvW
--
-- Its advantage is composability of more elementary sets. However, readability of proofs
-- diminishes. To illustrate this, consider another set of events:
-- > EvRWF = EvR ∪₁ EvW ∪₁ EvF
--
-- Pattern-matching on any instance of it will take the shape:
-- > foo (inj₁ (inj₁ x-r)) = ...
-- > foo (inj₁ (inj₂ y-w)) = ...
-- > foo (inj₂ x-f) = ...
--
-- Obtaining endless unions of sets makes the individual cases in proofs harder to read.
-- A (subjectively) preferable approach to the above pattern would be:
-- > foo (ev-r x-r) = ...
-- > foo (ev-w x-w) = ...
-- > foo (ev-f x-f) = ...
--
-- For this purpose, this library uses uniform constructor names between different
-- (but similar) data-types, and avoids the _∪₁_ whenever possible.
data EvRW : Pred₀ Event where
  ev-init : EvRW (event-init uid loc val)
  ev-r    : EvRW (event-r uid tid loc val lab-r)
  ev-w    : EvRW (event-w uid tid loc val lab-w)

-- | The set of Read/Write events indexed by their tag (mov/rmw)
data EvRWₜ (tag : Tag) : Pred₀ Event where
  ev-init : tag ≡ tmov → EvRWₜ tag (event-init uid loc val)
  ev-r    : tag ≡ lab-r-tag lab-r → EvRWₜ tag (event-r uid tid loc val lab-r)
  ev-w    : tag ≡ lab-w-tag lab-w → EvRWₜ tag (event-w uid tid loc val lab-w)
  
-- | The set of Read/Write events /without/ init events
data EvRWₙ : Pred₀ Event where
  ev-r : EvRWₙ (event-r uid tid loc val lab-r)
  ev-w : EvRWₙ (event-w uid tid loc val lab-w)

data EvRWₙₜ (tag : Tag) : Pred₀ Event where
  ev-r : tag ≡ lab-r-tag lab-r → EvRWₙₜ tag (event-r uid tid loc val lab-r)
  ev-w : tag ≡ lab-w-tag lab-w → EvRWₙₜ tag (event-w uid tid loc val lab-w)

-- r = relaxed (tmov)
-- a = atomic  (trmw)
EvRᵣ EvRₐ EvWᵣ EvWₐ EvWₙᵣ : Pred₀ Event
EvRᵣ  = EvRₜ tmov -- relaxed reads
EvRₐ  = EvRₜ trmw -- atomic reads
EvWᵣ  = EvWₜ tmov -- relaxed writes
EvWₐ  = EvWₜ trmw -- atomic writes
EvWₙᵣ = EvWₙₜ tmov -- relaxed non-init read
