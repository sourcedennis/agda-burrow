{-# OPTIONS --safe --without-K #-}

open import Burrow.Primitives

module Burrow.Execution.Core
  {arch : Arch}
  where
  
-- Library imports
open import Dodo.Unary using (Pred₀)
open import Dodo.Binary using (Rel₀)
-- Local imports
open import Burrow.Event.Core {arch}


-- # Definitions

-- ## Definitions: Execution

record Execution : Set₁ where
  field
    -- # Events
    
    events : Pred₀ Event


    -- # Relations between events
    
    -- ## Primitive relations

    -- | Program order
    po : Rel₀ Event -- E×E
    -- | Reads-from
    rf : Rel₀ Event -- W×R
    -- | Coherence order
    co : Rel₀ Event -- W×W


    -- ## Derived relations

    -- | Read-modify-write
    rmw : Rel₀ Event -- R×W
