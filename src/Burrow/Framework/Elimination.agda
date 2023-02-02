{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)


-- | A general framework for writing /elimination proofs/ on TCG executions.
--
-- An elimination operation always replaces a single non-atomic Read or Write event by a
-- Skip event.
module Burrow.Framework.Elimination
  {arch : Arch}
  {dst : Execution {arch}}
  (dst-wf : WellFormed dst)
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
open import Burrow.Event.Core {arch}
open import Burrow.Event.Pred
import Burrow.Framework.Definition arch {arch} dst-wf as Ψ
import Burrow.Framework.Primitives

open Execution
open Arch arch


private
  module Types
    (ev[⇐] : {x : Event} → (x∈ex : x ∈ events dst) → Event)
    (elim-ev : Event)
    where

    -- "C" stands for "Conditional". (i.e., conditional on not being eliminated)


    -- | For every non-eliminated element in the source, the predicate maps to the target.
    --
    -- Note: Rel₀ (Pred₀ Event)  ≜  (Event → Set) → (Event → Set) → Set
    CPred[$⇒] : Rel₀ (Pred₀ Event)
    CPred[$⇒] Pˢ Pᵗ = ∀ {x}
      → x ≢ elim-ev
      → (x∈dst : x ∈ events dst)
      → Pˢ (ev[⇐] x∈dst)
      → Pᵗ x
  
    -- | For every non-eliminated element in the source, the predicate maps to the target.
    --
    -- # Example:
    --
    -- > CPred[$⇒] po po
    --
    -- Inhabitants of that type declare: For every non-eliminated source event, the `po` relation
    -- remains preserved after mapping.
    CRel[$⇒] : Rel₀ (Rel₀ Event)
    CRel[$⇒] Rˢ Rᵗ = ∀ {x y}
      → x ≢ elim-ev → y ≢ elim-ev
      → (x∈dst : x ∈ events dst) (y∈dst : y ∈ events dst)
      → Rˢ (ev[⇐] x∈dst) (ev[⇐] y∈dst)
      → Rᵗ x y
  
    -- | For every non-eliminated element in the source, the predicate maps to the target.
    --
    -- The predicate is identical between source and target.
    CPred[$⇒]² : Pred₀ (Pred₀ Event)
    CPred[$⇒]² P = CPred[$⇒] P P

    CPred[⇐] : Rel₀ (Pred₀ Event)
    CPred[⇐] Pˢ Pᵗ = ∀ {x}
      → x ≢ elim-ev
      → (x∈dst : x ∈ events dst)
      → Pᵗ x
      → Pˢ (ev[⇐] x∈dst)


-- |
record EliminationFramework : Set₁ where
  field
    -- # Definitions
    ψ : Ψ.GeneralFramework
    
    -- | The event (in the target) that is eliminated
    elim-ev  : Event
    
    elim∈ex  : elim-ev ∈ events dst
    
    src-co   : Rel₀ Event
    src-rf   : Rel₀ Event

  open Ψ.GeneralFramework ψ using (ev[⇐])
  open Burrow.Framework.Primitives dst-wf ev[⇐] using (Pred[⇐]; Pred[$⇒]; Pred[⇐]²; Pred[$⇒]²; Rel[⇐])
  open Types ev[⇐] elim-ev public
  
  field
    -- # Definitions
    
    -- A transformation can only eliminate a /non-atomic/ Read or (non-init) Write instruction
    elim-r/w : EvRWₙₜ tmov (ev[⇐] elim∈ex)


    -- # Properties
    
    loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
    val[⇐] : {val : Value}    → Pred[⇐]² (HasVal val)
    Wₜ[⇐]  : {tag : Tag}      → Pred[⇐]² (EvWₜ tag)
    Rₜ[⇐]  : {tag : Tag}      → Pred[⇐]² (EvRₜ tag)
    F₌[⇐]  : {m : LabF}       → Pred[⇐] (EvFₜ m) (EvFₜ m)
    F₌[$⇒] : {m : LabF}       → Pred[$⇒] (EvFₜ m) (EvFₜ m)

    -- /atomic/ read/write events
    Wₐ[$⇒] : Pred[$⇒]² (EvWₜ trmw)
    Rₐ[$⇒] : Pred[$⇒]² (EvRₜ trmw)

    rf[⇐] : Rel[⇐] src-rf (rf dst)
    co[⇐] : Rel[⇐] src-co (co dst)

    -- These are conditional on not being eliminated
    
    -- /non-atomic/ read/write events
    Wᵣ[$⇒]   : CPred[$⇒]² (EvWₜ tmov)
    Rᵣ[$⇒]   : CPred[$⇒]² (EvRₜ tmov)
    
    loc[$⇒]  : {loc : Location} → CPred[$⇒]² (HasLoc loc)
    val[$⇒]  : {val : Value} → CPred[$⇒]² (HasVal val)

    rf[$⇒] : CRel[$⇒] src-rf (rf dst)
    co[$⇒] : CRel[$⇒] src-co (co dst)
