{-# OPTIONS --safe #-}

-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.WellFormed.Core using (WellFormed)
open import Relation.Unary using (_∈_)


-- | Template for architecture mapping proof (i.e., mapping between two different architectures)
module Burrow.Template.Mapping where

open import Burrow.Primitives public
open import Burrow.Execution.Core public
open import Burrow.WellFormed.Core public
open import Burrow.Event.Core public
open import Burrow.Event.Pred public
open import Burrow.Event.Rel public
open import Burrow.Event.Properties public

open Event public


module Defs where

  -- # Step 1: Define the mapping outcome
  --
  -- ```
  -- module MapXtoY where
  --
  -- open import Burrow.Template.Mapping as Δ
  --
  -- record X⇒Y (src : Execution {arch-X}) (dst : Execution {arch-Y}) where
  --   open Δ.Defs
  -- ```

  open import Burrow.Execution.Derived public
  open Execution public


module Restrict {archᵗ : Arch} (dst : Execution {archᵗ}) where

  -- # Step 2: Restrict the target
  --
  -- This restriction demonstrates that execution Y could only have been generated from a Y program
  -- that is mapped from an X program. (i.e., it follows from the syntax mapping)
  --
  -- ```
  -- record Y-XRestricted (ex : Execution {arch-Y}) : Set₁ where
  --   open Δ.Restrict ex
  -- ```
  --
  --
  -- # (optional) Step 3: Define Helpers
  --
  -- ```
  -- module Helpers {ex : Execution {arch-Y}} (ex-res : Y-XRestricted ex) where
  --
  -- open Δ.Restrict ex
  -- ```

  open Execution dst public
  open import Burrow.Execution.Derived dst public


module Primitives {archˢ archᵗ : Arch} {dst : Execution {archᵗ}}
  (dst-wf : WellFormed dst)
  (ev[⇐] : {x : Event {archᵗ}} → (x∈dst : x ∈ Execution.events dst) → Event {archˢ})
  where

  -- # Step 3: Define the backward mapping of events
  --
  -- Given `dst-wf : WellFormed dst`.
  --
  -- ```
  -- open Δ.Defs
  --
  -- ev[⇐] : {x : Event {archᵗ}}
  --   → (x∈dst : x ∈ events dst)
  --     ------------------------
  --   → Event {archˢ}
  -- ev[⇐] = ?
  -- ```
  --
  -- # Step 4: Instantiate the frameworks
  --
  -- ```
  -- open Δ.Primitives dst-wf ev[⇐]
  --
  -- δ : MappingFramework
  -- δ = ?
  -- ```

  open import Burrow.Framework.Primitives dst-wf ev[⇐] public
  open import Burrow.Framework.Definition archˢ dst-wf using (GeneralFramework) public
  open import Burrow.Framework.Mapping.Core archˢ dst-wf using (MappingFramework) public


import Burrow.Framework.Mapping.Core as FC

module Consistency
  {archˢ archᵗ : Arch}
  {dst : Execution {archᵗ}}
  {dst-wf : WellFormed dst}
  (δ : FC.MappingFramework archˢ dst-wf)
  where

  open import Burrow.Framework.Definition archˢ dst-wf using (GeneralFramework)
  open FC.MappingFramework
  open GeneralFramework

  open import Burrow.Framework.Primitives dst-wf (ev[⇐] (ψ δ)) public
  open import Burrow.Framework.Mapping.Definitions δ public
  open import Burrow.Framework.WellFormed (ψ δ) public
  open import Burrow.Framework.Mapping.WellFormed δ public
  open import Burrow.Execution.Derived public
  open import Burrow.WellFormed.Derived public
  
  open Execution public
  open WellFormed public


module Final
  {archˢ archᵗ : Arch}
  {dst : Execution {archᵗ}}
  {dst-wf : WellFormed dst}
  (δ : FC.MappingFramework archˢ dst-wf)
  where

  open Consistency δ public
  open import Burrow.Framework.Mapping.Behavior δ public
  
