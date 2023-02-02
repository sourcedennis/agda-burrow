{-# OPTIONS --safe --without-K #-}

open import Burrow.Primitives

module Burrow.Event.Core {arch : Arch} where


open Arch arch


-- # Definitions

-- ## Definitions: Event

-- | A generic event in an execution (w.r.t. axiomatic memory models)
-- Every architecture can define their own set of labels.
data Event : Set where
  -- Helper events that occur before the "real" events in the execution (in po and co)
  event-init  : UniqueId → Location → Value → Event
  -- Helper events that occur within a thread, but do /nothing/. These are useful when
  -- proving the mapping.
  event-skip  : UniqueId → ThreadId → Event
  
  event-r : UniqueId → ThreadId → Location → Value → LabR → Event
  event-w : UniqueId → ThreadId → Location → Value → LabW → Event
  event-f : UniqueId → ThreadId → LabF → Event
