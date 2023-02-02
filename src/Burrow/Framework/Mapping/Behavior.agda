{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Burrow.Framework.Mapping.Core using (MappingFramework)


-- | Derives `WellFormed` (for the source) generically from the `MappingFramework`.
module Burrow.Framework.Mapping.Behavior
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
open import Burrow.WellFormed.Core
open import Burrow.WellFormed.Derived
open import Burrow.Framework.Definition archˢ dst-wf as Ψ

open MappingFramework δ -- defines ψ
open Ψ.GeneralFramework ψ -- defines ev[⇐]

open import Burrow.Framework.Primitives dst-wf ev[⇐]
open import Burrow.Framework.WellFormed ψ
open Execution
open WellFormed

open import Burrow.Framework.Mapping.Definitions δ



-- # Behavior

proof-behavior : behavior src ⇔₂ behavior dst
proof-behavior = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : behavior src ⊆₂' behavior dst
  ⊆-proof loc val (x , x∈src , x-w , x-val , x-loc , x-co-max) =
    ev[⇒] x∈src , events[⇒] x∈src , W[⇒] x∈src x-w , val[⇒] x∈src x-val , loc[⇒] x∈src x-loc , dst-x-co-max
    where
    dst-x-co-max : maximal (co dst) (ev[⇒] x∈src)
    dst-x-co-max (y , co[xy]) =
      let y∈dst = coʳ∈ex dst-wf co[xy]
      in x-co-max (ev[⇐] y∈dst , co[⇐$] x∈src (events[⇐] y∈dst) co[xy])

  ⊇-proof : behavior dst ⊆₂' behavior src
  ⊇-proof loc val (x , x∈dst , x-w , x-val , x-loc , x-co-max) =
    ev[⇐] x∈dst , events[⇐] x∈dst , W[⇐] x∈dst x-w , val[⇐] x∈dst x-val , loc[⇐] x∈dst x-loc , src-x-co-max
    where
    src-x-co-max : maximal (co src) (ev[⇐] x∈dst)
    src-x-co-max (y , co[xy]) =
      let y∈src = coʳ∈src co[xy]
      in x-co-max (ev[⇒] y∈src , co[⇒] (events[⇐] x∈dst) y∈src co[xy])
