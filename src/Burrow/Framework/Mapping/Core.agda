{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)


module Burrow.Framework.Mapping.Core
  (archˢ : Arch)
  {archᵗ : Arch}
  {dst : Execution {archᵗ}}
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
open import Burrow.Event.Core
open import Burrow.Event.Pred
import Burrow.Framework.Definition archˢ dst-wf as Ψ
import Burrow.Framework.Primitives


-- | 
record MappingFramework : Set where
  field
    -- # Definitions
    ψ : Ψ.GeneralFramework

  open Ψ.GeneralFramework ψ
  open Burrow.Framework.Primitives dst-wf ev[⇐] using (Pred[⇐]²; Pred[$⇒]²)
  
  field
    -- # Properties
    
    loc[⇐]   : {loc : Location} → Pred[⇐]²  (HasLoc loc)
    loc[$⇒]  : {loc : Location} → Pred[$⇒]² (HasLoc loc)
    val[⇐]   : {val : Value}    → Pred[⇐]²  (HasVal val)
    val[$⇒]  : {val : Value}    → Pred[$⇒]² (HasVal val)
    Wₜ[⇐]    : {tag : Tag}      → Pred[⇐]²  (EvWₜ tag)
    Wₜ[$⇒]   : {tag : Tag}      → Pred[$⇒]² (EvWₜ tag)
    Rₜ[⇐]    : {tag : Tag}      → Pred[⇐]²  (EvRₜ tag)
    Rₜ[$⇒]   : {tag : Tag}      → Pred[$⇒]² (EvRₜ tag)
