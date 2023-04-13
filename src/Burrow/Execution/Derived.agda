{-# OPTIONS --safe --without-K #-}

open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)

module Burrow.Execution.Derived
  {arch : Arch}
  (ex : Execution {arch})
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (flip)
-- Local library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Burrow.Event.Core {arch}
open import Burrow.Event.Pred
open import Burrow.Event.Rel


-- There are multiple ways of defining internal/external relations.
-- An alternative way (to the one below) is defining:
--
-- internal r = r ∩₂ po
--
-- However, we actually want to claim that iff some `x` and `y`
-- are related by an internal relation, then they are also related
-- by `po`. Which means:
--
-- > internal r = r ∩₂ (po ∪₂ flip po)
--
-- After all, `x` and `y` are po-related iff `po x y` or `po y x`
-- holds. `SameTid` - together with wellformedness - ensures
-- `po x y` or `po y x` holds. (E.g., see `po-tri`)
--
-- So, we could alternative define this as:
--
-- > internal r = r ∩₂ SameTid
--
-- Though, at this point, I'm not sure which is better. Keep this explanation
-- around to assist in that decision later.


open Execution ex


-- ## Definitions: Execution Relation Helpers

-- | internal. relates po-related events.
--
-- We also include _≡_, which relates events to themselves. Otherwise, an event
-- would be external to itself, which makes no sense either.
int : Rel₀ Event
int = po ∪₂ flip po ∪₂ _≡_

ext : Rel₀ Event
ext = ¬₂ int

internal :
    Rel₀ Event
    ----------
  → Rel₀ Event
internal R = R ∩₂ int

external :
    Rel₀ Event
    ----------
  → Rel₀ Event
external R = R ∩₂ ext

internal⊆ :
    (R : Rel₀ Event)
    ----------------
  → internal R ⊆₂ R
internal⊆ R = ∩₂-introʳ-⊆₂

external⊆ :
    (R : Rel₀ Event)
    ----------------
  → external R ⊆₂ R
external⊆ R = ∩₂-introʳ-⊆₂


-- # Definitions: Derived Execution Relations

-- | From-read derived relation (R×W)
fr : Rel₀ Event
fr = flip rf ⨾ co

-- | Same-location events along the program order
po-loc : Rel₀ Event
po-loc = po ∩₂ SameLoc

po-imm : Rel₀ Event
po-imm = immediate po

-- | External read-from relation
rfe : Rel₀ Event
rfe = external rf

-- | Internal read-from relation
rfi : Rel₀ Event
rfi = internal rf

-- | External coherence-order relation
coe : Rel₀ Event
coe = external co

-- | Internal coherence-order relation
coi : Rel₀ Event
coi = internal co

-- | External from-read relation
fre : Rel₀ Event
fre = external fr

-- | Internal from-read relation
fri : Rel₀ Event
fri = internal fr

-- `po` between non-skip events.
-- skip events are merely an artifact of our proof structure.
-- intuitively, they are NOPs. they are not ordered with anything.
po-no-skip : Rel₀ Event
po-no-skip = po ∩₂ ((¬₁ EvSkip)  ×₂  (¬₁ EvSkip))
