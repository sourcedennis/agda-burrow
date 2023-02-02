{-# OPTIONS --safe #-}


-- | A template for defining a new axiomatic architecture model.
module Burrow.Template.Arch where

-- # Step 1: Define the instance of `Arch`
--
-- ```
-- open import Burrow.Template.Arch as Π
--
-- -- Definitions here
--
-- arch-x : Arch
-- arch-x = ?
-- ```

open import Burrow.Primitives public
open import Burrow.Execution.Core using (Execution) public
open import Burrow.WellFormed.Core using (WellFormed) public


module Ev (arch : Arch) where

  -- # (optional) Step 1b: Define helpers over `Event`
  --
  -- ```
  -- open Π.Ev arch-x
  -- ```

  open import Burrow.Event.Core {arch} public
  open import Burrow.Event.Properties public
  open import Burrow.Event.Pred public
  open import Burrow.Event.Rel public


module Defs {arch : Arch} (ex : Execution {arch}) where

  -- # Step 2: Define the architecture-specific relations and consistency rules
  --
  -- ```
  -- module Relations (ex : Execution {arch-x}) where
  --
  -- open Π.Defs ex
  --
  -- record IsConsistent : Set where
  --   field
  -- ```

  open Execution ex public
  open import Burrow.Execution.Core {arch} as Ex public
  open import Burrow.Execution.Derived ex public


module WfDefs {arch : Arch} {ex : Execution {arch}} (wf : WellFormed ex) where

  -- # (optional) Step 3: Define architecture-specific properties
  --
  -- ```
  -- module Properties {ex : Execution {arch-TCG}} (wf : WellFormed ex) where
  --
  -- open Relations ex
  -- open Π.WfDefs wf
  -- ```

  open WellFormed wf public
  open import Burrow.WellFormed.Derived wf public
