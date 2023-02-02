{-# OPTIONS --safe --without-K #-}

open import Burrow.Primitives

module Burrow.Event.Rel
  {arch₁ arch₂ : Arch}
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong-app; sym; subst; subst₂)
open import Level using () renaming (zero to ℓzero)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; Empty)
-- Local imports
open import Burrow.Event.Pred using (HasUid; HasTid; HasLoc; HasVal; HasTag)


private
  variable
    uid : UniqueId
    tid : ThreadId
    loc : Location
    val : Value
    tag : Tag


open import Burrow.Event.Core {arch₁} using () renaming (Event to Event₁)
open import Burrow.Event.Core {arch₂} using () renaming (Event to Event₂)

-- # Binary Predicates

-- | Effectively: ∃[ uid ] (HasUid uid a × HasUid uid b)
data SameUid (a : Event₁) (b : Event₂) : Set where
  same-uid : HasUid uid a → HasUid uid b → SameUid a b
  
-- | Effectively: ∃[ tid ] (HasTid tid a × HasTid tid b)
data SameTid (a : Event₁) (b : Event₂) : Set where
  same-tid : HasTid tid a → HasTid tid b → SameTid a b

-- | Effectively: ∃[ loc ] (HasLoc loc a × HasLoc loc b)
data SameLoc (a : Event₁) (b : Event₂) : Set where
  same-loc : HasLoc loc a → HasLoc loc b → SameLoc a b

-- | Effectively: ∃[ val ] (HasVal val a × HasVal val b)
data SameVal (a : Event₁) (b : Event₂) : Set where
  same-val : HasVal val a → HasVal val b → SameVal a b

-- | Effectively: ∃[ tag ] (HasTag tag a × HasTag tag b)
data SameTag (a : Event₁) (b : Event₂) : Set where
  same-tag : HasTag tag a → HasTag tag b → SameTag a b
