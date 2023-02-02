{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)


module Burrow.Framework.Definition
  (archˢ : Arch)
  {archᵗ : Arch}
  {dst : Execution {archᵗ}}
  (dst-wf : WellFormed dst)
  where

-- Stdlib imports
open import Relation.Unary using (_∈_)
-- Local imports
open import Burrow.Primitives
open import Burrow.Event.Core using (Event)
open import Burrow.Event.Pred
import Burrow.Framework.Primitives {archˢ} dst-wf as P


private
  Eventˢ = Event {archˢ}
  Eventᵗ = Event {archᵗ}
    
open Execution


record GeneralFramework : Set where
  field
    ev[⇐]    : {xᵗ : Eventᵗ} → (x∈dst : xᵗ ∈ events dst) → Eventˢ

  -- This seems to work. Interesting..
  open P ev[⇐] using (Pred[⇐]²; Pred[$⇒]²)

  field
    -- # Properties

    uid[⇐]   : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
    uid[$⇒]  : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
    tid[⇐]   : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
    tid[$⇒]  : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
    Init[⇐]  : Pred[⇐]² EvInit
    Init[$⇒] : Pred[$⇒]² EvInit
