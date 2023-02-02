{-# OPTIONS --safe --without-K #-}

open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)

module Burrow.Execution.Derived
  {arch : Arch}
  (ex : Execution {arch})
  where

-- Stdlib imports
open import Function using (flip)
-- Local library imports
open import Dodo.Binary
-- Local imports
open import Burrow.Event.Core {arch}
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

internal :
    Rel₀ Event
    ----------
  → Rel₀ Event
internal R = R ∩₂ po

external :
    Rel₀ Event
    ----------
  → Rel₀ Event
external R = R ∩₂ (¬₂ po)

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
