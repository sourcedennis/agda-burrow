{-# OPTIONS --safe #-}


-- | Properties and operations for events.
module Burrow.Event.Properties where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂) renaming (sym to ≡-sym; trans to ≡-trans)
-- open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃-syntax; _,_; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Burrow.Primitives
open import Burrow.Internal.Helpers


module ₁ {arch : Arch} where

  open import Burrow.Event.Core {arch}
  open import Burrow.Event.Pred {arch}
  open import Burrow.Event.Rel {arch}

  open Arch arch
  

  -- # General

  -- | Every event has a unique identifier
  ev-uid : Event → UniqueId
  ev-uid (event-init uid _ _)  = uid
  ev-uid (event-skip uid _)    = uid
  ev-uid (event-r uid _ _ _ _) = uid
  ev-uid (event-w uid _ _ _ _) = uid
  ev-uid (event-f uid _ _)     = uid

  -- | Every event has a witness of its Unique ID
  ev-has-uid : (ev : Event) → HasUid (ev-uid ev) ev
  ev-has-uid (event-init _ _ _)  = has-uid-init
  ev-has-uid (event-skip _ _)    = has-uid-skip
  ev-has-uid (event-r _ _ _ _ _) = has-uid-r
  ev-has-uid (event-w _ _ _ _ _) = has-uid-w
  ev-has-uid (event-f _ _ _)     = has-uid-f

  has-uid-dec : (uid : UniqueId) → DecPred (HasUid uid)
  has-uid-dec uid x with uid-dec≡ (ev-uid x) uid
  ... | yes refl = yes (ev-has-uid x)
  ... | no  ¬uid = no lemma
    where
    lemma : ¬ HasUid uid x
    lemma has-uid-init = ¬uid refl
    lemma has-uid-skip = ¬uid refl
    lemma has-uid-r    = ¬uid refl
    lemma has-uid-w    = ¬uid refl
    lemma has-uid-f    = ¬uid refl

  -- | Every /skip/ event has a Thread ID
  skip-tid : {ev : Event} → EvSkip ev → ThreadId
  skip-tid {ev = event-skip _ tid} ev-skip = tid

  -- | Every /skip/ event has a witness of its Thread ID
  skip-has-tid : {ev : Event} (ev-skip : EvSkip ev) → HasTid (skip-tid ev-skip) ev
  skip-has-tid ev-skip = has-tid-skip

  -- | Every event is either a init event, or it has a Thread ID
  ev-init/tid : XOptPred₂ EvInit HasSomeTid
  ev-init/tid (event-init _ _ _)    = xopt₁ ev-init (λ())
  ev-init/tid (event-skip _ tid)    = xopt₂ (λ()) (tid , has-tid-skip)
  ev-init/tid (event-r _ tid _ _ _) = xopt₂ (λ()) (tid , has-tid-r)
  ev-init/tid (event-w _ tid _ _ _) = xopt₂ (λ()) (tid , has-tid-w)
  ev-init/tid (event-f _ tid _)     = xopt₂ (λ()) (tid , has-tid-f)

  disjoint-init/tid : {tid : ThreadId} → Disjoint₁ EvInit (HasTid tid)
  disjoint-init/tid _ (ev-init , ())


  -- ## Operations: Set splits

  r/tag : {x : Event} → EvR x → (EvRₜ tmov ∪₁ EvRₜ trmw) x
  r/tag {event-r _ _ _ _ lab-r} ev-r with inspect (lab-r-tag lab-r)
  ... | tmov with≡ tag≡tmov = inj₁ (ev-r (≡-sym tag≡tmov))
  ... | trmw with≡ tag≡trmw = inj₂ (ev-r (≡-sym tag≡trmw))

  w/tag : {x : Event} → EvW x → (EvWₜ tmov ∪₁ EvWₜ trmw) x
  w/tag ev-init = inj₁ (ev-init refl)
  w/tag {event-w _ _ _ _ lab-w} ev-w with inspect (lab-w-tag lab-w)
  ... | tmov with≡ tag≡tmov = inj₁ (ev-w (≡-sym tag≡tmov))
  ... | trmw with≡ tag≡trmw = inj₂ (ev-w (≡-sym tag≡trmw))

  wᵣ/init : {x : Event} → EvWᵣ x → (EvInit ∪₁ EvWₙᵣ) x
  wᵣ/init (ev-init refl)  = inj₁ ev-init
  wᵣ/init (ev-w tmov≡tag) = inj₂ (ev-w tmov≡tag)

  rw/rw : {x : Event} → EvRW x → (EvR ∪₁ EvW) x
  rw/rw ev-init = inj₂ ev-init
  rw/rw ev-r    = inj₁ ev-r
  rw/rw ev-w    = inj₂ ev-w

  rwₜ/rw : {x : Event} {tag : Tag} → EvRWₜ tag x → (EvRₜ tag ∪₁ EvWₜ tag) x
  rwₜ/rw (ev-init refl) = inj₂ (ev-init refl)
  rwₜ/rw (ev-r refl)    = inj₁ (ev-r refl)
  rwₜ/rw (ev-w refl)    = inj₂ (ev-w refl)

  rwₙₜ/rw : {x : Event} {tag : Tag} → EvRWₙₜ tag x → (EvRₜ tag ∪₁ EvWₙₜ tag) x
  rwₙₜ/rw (ev-r refl) = inj₁ (ev-r refl)
  rwₙₜ/rw (ev-w refl) = inj₂ (ev-w refl)

  rw/tag : {x : Event} → EvRW x → (EvRWₜ tmov ∪₁ EvRWₜ trmw) x
  rw/tag ev-init = inj₁ (ev-init refl)
  rw/tag {event-r _ _ _ _ lab-r} ev-r with inspect (lab-r-tag lab-r)
  ... | tmov with≡ tag≡tmov = inj₁ (ev-r (≡-sym tag≡tmov))
  ... | trmw with≡ tag≡trmw = inj₂ (ev-r (≡-sym tag≡trmw))
  rw/tag {event-w _ _ _ _ lab-w} ev-w with inspect (lab-w-tag lab-w)
  ... | tmov with≡ tag≡tmov = inj₁ (ev-w (≡-sym tag≡tmov))
  ... | trmw with≡ tag≡trmw = inj₂ (ev-w (≡-sym tag≡trmw))

  -- | Every read event has a location
  r-loc : {ev : Event} → EvR ev → Location
  r-loc {event-r _ _ loc _ _} ev-r = loc

  -- | Every read event has a witness of its location
  r-has-loc : {ev : Event} → (ev-r : EvR ev) → HasLoc (r-loc ev-r) ev
  r-has-loc ev-r = has-loc-r

  -- | Every read event has a value
  r-val : {ev : Event} → EvR ev → Value
  r-val {event-r _ _ _ val _} ev-r = val

  -- | Every read event has a witness of its value
  r-has-val : {ev : Event} → (ev-r : EvR ev) → HasVal (r-val ev-r) ev
  r-has-val ev-r = has-val-r

  -- | Every read event has a tag
  r-tag : {ev : Event} → (ev-r : EvR ev) → Tag
  r-tag {event-r _ _ _ _ lab-r} ev-r = lab-r-tag lab-r

  -- | Every write event has a location
  w-loc : {ev : Event} → EvW ev → Location
  w-loc {event-init _ loc _} ev-init = loc
  w-loc {event-w _ _ loc _ _} ev-w = loc

  -- | Every write event has a witness of its location
  w-has-loc : {ev : Event} → (ev-w : EvW ev) → HasLoc (w-loc ev-w) ev
  w-has-loc ev-init = has-loc-init
  w-has-loc ev-w    = has-loc-w

  -- | Every write event has a value
  w-val : {ev : Event} → EvW ev → Value
  w-val {event-init _ _ val}  ev-init = val
  w-val {event-w _ _ _ val _} ev-w    = val

  -- | Every write event has a witness of its location
  w-has-val : {ev : Event} → (ev-w : EvW ev) → HasVal (w-val ev-w) ev
  w-has-val ev-init = has-val-init
  w-has-val ev-w    = has-val-w

  -- | Every write event has a tag
  w-tag : {ev : Event} → EvW ev → Tag
  w-tag ev-init = tmov
  w-tag {event-w _ _ _ _ lab-w} ev-w = lab-w-tag lab-w

  ¬f-loc : {ev : Event} → EvF ev → ¬ (∃[ loc ] HasLoc loc ev)
  ¬f-loc ev-f ()
  
  ¬f-val : {ev : Event} → EvF ev → ¬ (∃[ val ] HasVal val ev)
  ¬f-val ev-f ()

  ¬skip-loc : {ev : Event} → EvSkip ev → ¬ (∃[ loc ] HasLoc loc ev)
  ¬skip-loc ev-skip ()

  ¬skip-val : {ev : Event} → EvSkip ev → ¬ (∃[ val ] HasVal val ev)
  ¬skip-val ev-skip ()

  rw-tag : {ev : Event} → EvRW ev → Tag
  rw-tag x-rw with rw/rw x-rw
  ... | inj₁ x-r = r-tag x-r
  ... | inj₂ x-w = w-tag x-w

  -- | Every init event has a location
  init-loc : {ev : Event} → EvInit ev → Location
  init-loc {event-init _ loc _} ev-init = loc

  -- | Every init event has a location
  init-has-loc : {ev : Event} → (ev-init : EvInit ev) → HasLoc (init-loc ev-init) ev
  init-has-loc ev-init = has-loc-init

  -- | Every init event has a value
  init-val : {ev : Event} → EvInit ev → Value
  init-val {ev = event-init _ _ val} ev-init = val

  -- | Every init event has a location
  init-has-val : {ev : Event} → (ev-init : EvInit ev) → HasVal (init-val ev-init) ev
  init-has-val ev-init = has-val-init

  -- | Every event is in the set of events (E).
  ev-e : (ev : Event) → EvE ev
  ev-e (event-init _ _ _)  = ev-init
  ev-e (event-skip _ _)    = ev-skip
  ev-e (event-r _ _ _ _ _) = ev-r
  ev-e (event-w _ _ _ _ _) = ev-w
  ev-e (event-f _ _ _)     = ev-f


  -- # Operations

  -- ### Operations - Coercion: Sets

  r⇒rₜ : {ev : Event} → (ev-r : EvR ev) → EvRₜ (r-tag ev-r) ev
  r⇒rₜ ev-r = ev-r refl

  rₜ⇒r : {ev : Event} {tag : Tag} → EvRₜ tag ev → EvR ev
  rₜ⇒r (ev-r _) = ev-r

  r⇒rw : {ev : Event} → EvR ev → EvRW ev
  r⇒rw ev-r = ev-r

  rₜ⇒rwₙₜ : {ev : Event} {tag : Tag} → EvRₜ tag ev → EvRWₙₜ tag ev
  rₜ⇒rwₙₜ (ev-r p) = ev-r p

  rₜ⇒rwₜ : {ev : Event} {tag : Tag} → EvRₜ tag ev → EvRWₜ tag ev
  rₜ⇒rwₜ (ev-r p) = ev-r p

  rₜ⇒rw : {ev : Event} {tag : Tag} → EvRₜ tag ev → EvRW ev
  rₜ⇒rw = r⇒rw ∘ rₜ⇒r

  w⇒wₜ : {ev : Event} → (ev-w : EvW ev) → EvWₜ (w-tag ev-w) ev
  w⇒wₜ ev-init = ev-init refl
  w⇒wₜ ev-w    = ev-w refl

  wₜ⇒w : {ev : Event} {tag : Tag} → EvWₜ tag ev → EvW ev
  wₜ⇒w (ev-init _) = ev-init
  wₜ⇒w (ev-w _)    = ev-w

  w⇒rw : {ev : Event} → EvW ev → EvRW ev
  w⇒rw ev-init = ev-init
  w⇒rw ev-w    = ev-w

  wₜ⇒rwₜ : {ev : Event} {tag : Tag} → EvWₜ tag ev → EvRWₜ tag ev
  wₜ⇒rwₜ (ev-init p) = ev-init p
  wₜ⇒rwₜ (ev-w p)    = ev-w p

  wₙₜ⇒rwₙₜ : {ev : Event} {tag : Tag} → EvWₙₜ tag ev → EvRWₙₜ tag ev
  wₙₜ⇒rwₙₜ (ev-w p) = ev-w p

  wₜ⇒rw : {ev : Event} {tag : Tag} → EvWₜ tag ev → EvRW ev
  wₜ⇒rw = w⇒rw ∘ wₜ⇒w

  wₙₜ⇒wₜ : {ev : Event} {tag : Tag} → EvWₙₜ tag ev → EvWₜ tag ev
  wₙₜ⇒wₜ (ev-w p) = ev-w p

  wₙₜ⇒w : {ev : Event} {tag : Tag} → EvWₙₜ tag ev → EvW ev
  wₙₜ⇒w = wₜ⇒w ∘ wₙₜ⇒wₜ

  wₙₜ⇒wₙ : {ev : Event} {tag : Tag} → EvWₙₜ tag ev → EvWₙ ev
  wₙₜ⇒wₙ (ev-w _) = ev-w

  rwₜ⇒rw : {ev : Event} {tag : Tag} → EvRWₜ tag ev → EvRW ev
  rwₜ⇒rw (ev-init _) = ev-init
  rwₜ⇒rw (ev-w _)    = ev-w
  rwₜ⇒rw (ev-r _)    = ev-r

  rw⇒rwₜ : {ev : Event} → (ev-rw : EvRW ev) → EvRWₜ (rw-tag ev-rw) ev
  rw⇒rwₜ ev-init = ev-init refl
  rw⇒rwₜ ev-w    = ev-w refl
  rw⇒rwₜ ev-r    = ev-r refl

  rwₙₜ⇒rwₜ : {ev : Event} {tag : Tag} → EvRWₙₜ tag ev → EvRWₜ tag ev
  rwₙₜ⇒rwₜ (ev-w p) = ev-w p
  rwₙₜ⇒rwₜ (ev-r p) = ev-r p

  init⇒wₜ : {ev : Event} → EvInit ev → EvWₜ tmov ev
  init⇒wₜ ev-init = ev-init refl

  fₜ⇒f : {ev : Event} {lab : LabF} → EvFₜ lab ev → EvF ev
  fₜ⇒f {event-f _ _ _} ev-f = ev-f

  f⇒e : {ev : Event} → EvF ev → EvE ev
  f⇒e ev-f = ev-f

  rw⇒e : {ev : Event} → EvRW ev → EvE ev
  rw⇒e ev-init = ev-init
  rw⇒e ev-r    = ev-r
  rw⇒e ev-w    = ev-w

  r⇒e : {ev : Event} → EvR ev → EvE ev
  r⇒e = rw⇒e ∘ r⇒rw

  w⇒e : {ev : Event} → EvW ev → EvE ev
  w⇒e = rw⇒e ∘ w⇒rw


  -- # Properties

  -- ## Properties: Uniqueness

  -- ### Properties - Uniqueness: Values

  -- | The UID of an event is unique.
  --
  -- That is, every event has at most one UID.
  uid-unique : {ev : Event} → Unique₁ _≡_ (λ uid → HasUid uid ev)
  uid-unique has-uid-init has-uid-init = refl
  uid-unique has-uid-skip has-uid-skip = refl
  uid-unique has-uid-r    has-uid-r    = refl
  uid-unique has-uid-w    has-uid-w    = refl
  uid-unique has-uid-f    has-uid-f    = refl

  -- | The Thread ID of an event is unique.
  --
  -- That is, every event has at most one Thread ID.
  tid-unique : {ev : Event} → Unique₁ _≡_ (λ tid → HasTid tid ev)
  tid-unique has-tid-skip has-tid-skip = refl
  tid-unique has-tid-r    has-tid-r    = refl
  tid-unique has-tid-w    has-tid-w    = refl
  tid-unique has-tid-f    has-tid-f    = refl


  -- | The location of an event is unique.
  --
  -- That is, every event has at most one location.
  loc-unique : {ev : Event} → Unique₁ _≡_ (λ loc → HasLoc loc ev)
  loc-unique has-loc-init has-loc-init = refl
  loc-unique has-loc-r    has-loc-r    = refl
  loc-unique has-loc-w    has-loc-w    = refl

  -- | The value of an event is unique.
  --
  -- That is, every event has at most one value.
  val-unique : {ev : Event} → Unique₁ _≡_ (λ val → HasVal val ev)
  val-unique has-val-init has-val-init = refl
  val-unique has-val-r    has-val-r    = refl
  val-unique has-val-w    has-val-w    = refl


  -- ### Properties - Uniqueness: Proofs

  -- | The proof that an event has a particular UID is unique.
  has-uid-unique : {uid : UniqueId} → UniquePred (HasUid uid)
  has-uid-unique _ has-uid-init has-uid-init = refl
  has-uid-unique _ has-uid-skip has-uid-skip = refl
  has-uid-unique _ has-uid-r    has-uid-r    = refl
  has-uid-unique _ has-uid-w    has-uid-w    = refl
  has-uid-unique _ has-uid-f    has-uid-f    = refl

  -- | The proof that an event has a particular Thread ID is unique.
  has-tid-unique : {tid : ThreadId} → UniquePred (HasTid tid)
  has-tid-unique _ has-tid-skip has-tid-skip = refl
  has-tid-unique _ has-tid-r    has-tid-r    = refl
  has-tid-unique _ has-tid-w    has-tid-w    = refl
  has-tid-unique _ has-tid-f    has-tid-f    = refl

  has-loc-unique : {loc : Location} → UniquePred (HasLoc loc)
  has-loc-unique _ has-loc-init has-loc-init = refl
  has-loc-unique _ has-loc-r    has-loc-r    = refl
  has-loc-unique _ has-loc-w    has-loc-w    = refl

  has-val-unique : {val : Value} → UniquePred (HasVal val)
  has-val-unique _ has-val-init has-val-init = refl
  has-val-unique _ has-val-r    has-val-r    = refl
  has-val-unique _ has-val-w    has-val-w    = refl

  w-unique : UniquePred EvW
  w-unique _ ev-init ev-init = refl
  w-unique _ ev-w    ev-w    = refl

  r-unique : UniquePred EvR
  r-unique _ ev-r ev-r = refl
  
  f-unique : UniquePred EvF
  f-unique _ ev-f ev-f = refl
  
  init-unique : UniquePred EvInit
  init-unique _ ev-init ev-init = refl

  skip-unique : UniquePred EvSkip
  skip-unique _ ev-skip ev-skip = refl

  -- ## Operations: Substitution

  -- ### Operations - Subsititution: Predicates

  subst-uid : {ev : Event} {u₁ u₂ : UniqueId}
    → u₁ ≡ u₂
    → HasUid u₁ ev
      ------------
    → HasUid u₂ ev
  subst-uid refl has-uid-init = has-uid-init
  subst-uid refl has-uid-skip = has-uid-skip
  subst-uid refl has-uid-r    = has-uid-r
  subst-uid refl has-uid-w    = has-uid-w
  subst-uid refl has-uid-f    = has-uid-f

  subst-tid : {ev : Event} {t₁ t₂ : ThreadId}
    → t₁ ≡ t₂
    → HasTid t₁ ev
      ------------
    → HasTid t₂ ev
  subst-tid refl has-tid-skip = has-tid-skip
  subst-tid refl has-tid-r    = has-tid-r
  subst-tid refl has-tid-w    = has-tid-w
  subst-tid refl has-tid-f    = has-tid-f

  subst-loc : {ev : Event} {l₁ l₂ : Location}
    → l₁ ≡ l₂
    → HasLoc l₁ ev
      ------------
    → HasLoc l₂ ev
  subst-loc refl has-loc-init = has-loc-init
  subst-loc refl has-loc-r    = has-loc-r
  subst-loc refl has-loc-w    = has-loc-w

  subst-val : {ev : Event} {v₁ v₂ : Value}
    → v₁ ≡ v₂
    → HasVal v₁ ev
      ------------
    → HasVal v₂ ev
  subst-val refl has-val-init = has-val-init
  subst-val refl has-val-r    = has-val-r
  subst-val refl has-val-w    = has-val-w

  ev-dec≡ : Dec≡ Event
  ev-dec≡ (event-init uid₁ loc₁ val₁) (event-init uid₂ loc₂ val₂) =
    cong₃-dec≡ event-init
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (uid-dec≡ uid₁ uid₂) (loc-dec≡ loc₁ loc₂) (val-dec≡ val₁ val₂)
  ev-dec≡ (event-skip uid₁ tid₁) (event-skip uid₂ tid₂) =
    cong₂-dec≡ event-skip
      (λ{refl → refl}) (λ{refl → refl})
      (uid-dec≡ uid₁ uid₂) (tid-dec≡ tid₁ tid₂)
  ev-dec≡ (event-r uid₁ tid₁ loc₁ val₁ lab₁) (event-r uid₂ tid₂ loc₂ val₂ lab₂) =
    cong₅-dec≡ event-r
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (uid-dec≡ uid₁ uid₂) (tid-dec≡ tid₁ tid₂) (loc-dec≡ loc₁ loc₂) (val-dec≡ val₁ val₂) (lab-r-dec≡ lab₁ lab₂)
  ev-dec≡ (event-w uid₁ tid₁ loc₁ val₁ lab₁) (event-w uid₂ tid₂ loc₂ val₂ lab₂) =
    cong₅-dec≡ event-w
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (uid-dec≡ uid₁ uid₂) (tid-dec≡ tid₁ tid₂) (loc-dec≡ loc₁ loc₂) (val-dec≡ val₁ val₂) (lab-w-dec≡ lab₁ lab₂)
  ev-dec≡ (event-f uid₁ tid₁ lab₁) (event-f uid₂ tid₂ lab₂) =
    cong₃-dec≡ event-f
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (uid-dec≡ uid₁ uid₂) (tid-dec≡ tid₁ tid₂) (lab-f-dec≡ lab₁ lab₂)
  -- false cases
  ev-dec≡ (event-init _ _ _)  (event-skip _ _)    = no (λ())
  ev-dec≡ (event-init _ _ _)  (event-r _ _ _ _ _) = no (λ())
  ev-dec≡ (event-init _ _ _)  (event-w _ _ _ _ _) = no (λ())
  ev-dec≡ (event-init _ _ _)  (event-f _ _ _)     = no (λ())
  ev-dec≡ (event-skip _ _)    (event-init _ _ _)  = no (λ())
  ev-dec≡ (event-skip _ _)    (event-r _ _ _ _ _) = no (λ())
  ev-dec≡ (event-skip _ _)    (event-w _ _ _ _ _) = no (λ())
  ev-dec≡ (event-skip _ _)    (event-f _ _ _)     = no (λ())
  ev-dec≡ (event-r _ _ _ _ _) (event-init _ _ _)  = no (λ())
  ev-dec≡ (event-r _ _ _ _ _) (event-skip _ _)    = no (λ())
  ev-dec≡ (event-r _ _ _ _ _) (event-w _ _ _ _ _) = no (λ())
  ev-dec≡ (event-r _ _ _ _ _) (event-f _ _ _)     = no (λ())
  ev-dec≡ (event-w _ _ _ _ _) (event-init _ _ _)  = no (λ())
  ev-dec≡ (event-w _ _ _ _ _) (event-skip _ _)    = no (λ())
  ev-dec≡ (event-w _ _ _ _ _) (event-r _ _ _ _ _) = no (λ())
  ev-dec≡ (event-w _ _ _ _ _) (event-f _ _ _)     = no (λ())
  ev-dec≡ (event-f _ _ _)     (event-init _ _ _)  = no (λ())
  ev-dec≡ (event-f _ _ _)     (event-skip _ _)    = no (λ())
  ev-dec≡ (event-f _ _ _)     (event-r _ _ _ _ _) = no (λ())
  ev-dec≡ (event-f _ _ _)     (event-w _ _ _ _ _) = no (λ())


  -- ## Properties: Set Relations

  Init⊆W : EvInit ⊆₁ EvW
  Init⊆W = ⊆: λ{_ ev-init → ev-init}

  R⊆RW : EvR ⊆₁ EvRW
  R⊆RW = ⊆: λ{_ → r⇒rw}

  W⊆RW : EvW ⊆₁ EvRW
  W⊆RW = ⊆: λ{_ → w⇒rw}

  R⊆E : EvR ⊆₁ EvE
  R⊆E = ⊆: λ{_ → r⇒e}

  W⊆E : EvW ⊆₁ EvE
  W⊆E = ⊆: λ{_ → w⇒e}

  F⊆E : EvF ⊆₁ EvE
  F⊆E = ⊆: λ{_ → f⇒e}

  W⊆SomeLoc : EvW ⊆₁ HasSomeLoc
  W⊆SomeLoc = ⊆: (λ{_ → < w-loc , w-has-loc >})

  R⊆SomeLoc : EvR ⊆₁ HasSomeLoc
  R⊆SomeLoc = ⊆: (λ{_ → < r-loc , r-has-loc >})

  W⊆SomeVal : EvW ⊆₁ HasSomeVal
  W⊆SomeVal = ⊆: (λ{_ → < w-val , w-has-val >})

  R⊆SomeVal : EvR ⊆₁ HasSomeVal
  R⊆SomeVal = ⊆: (λ{_ → < r-val , r-has-val >})


  -- ## Properties: Disjoint Sets

  disjoint-r/w : Disjoint₁ EvR EvW
  disjoint-r/w _ (ev-r , ())
  
  disjoint-r/wf : Disjoint₁ EvR (EvW ∪₁ EvF)
  disjoint-r/wf _ (ev-r , inj₁ ())
  disjoint-r/wf _ (ev-r , inj₂ ())
  
  disjoint-w/rf : Disjoint₁ EvW (EvR ∪₁ EvF)
  disjoint-w/rf _ (ev-w , inj₁ ())
  disjoint-w/rf _ (ev-w , inj₂ ())

  disjoint-f/r : Disjoint₁ EvF EvR
  disjoint-f/r _ (ev-f , ())

  disjoint-f/w : Disjoint₁ EvF EvW
  disjoint-f/w _ (ev-f , ())

  disjoint-f/rw : Disjoint₁ EvF EvRW
  disjoint-f/rw _ (ev-f , ())
  
  disjoint-f/r∪w : Disjoint₁ EvF (EvR ∪₁ EvW)
  disjoint-f/r∪w _ (ev-f , inj₁ ())
  disjoint-f/r∪w _ (ev-f , inj₂ ())
  
  disjoint-r/init : Disjoint₁ EvR EvInit
  disjoint-r/init _ (ev-r , ())

  disjoint-wₜ/init : Disjoint₁ (EvWₜ trmw) EvInit
  disjoint-wₜ/init _ (ev-init () , ev-init)

  disjoint-wₙ/init : Disjoint₁ EvWₙ EvInit
  disjoint-wₙ/init _ (() , ev-init)

  disjoint-f/init : Disjoint₁ EvF EvInit
  disjoint-f/init _ (() , ev-init)

  disjoint-skip/init : Disjoint₁ EvSkip EvInit
  disjoint-skip/init _ (ev-skip , ())

  disjoint-r/skip : Disjoint₁ EvR EvSkip
  disjoint-r/skip _ (() , ev-skip)

  disjoint-w/skip : Disjoint₁ EvW EvSkip
  disjoint-w/skip _ (() , ev-skip)

  disjoint-f/skip : Disjoint₁ EvF EvSkip
  disjoint-f/skip _ (() , ev-skip)

  disjoint-init/rwₙₜ : Disjoint₁ EvInit (EvRWₙₜ tmov)
  disjoint-init/rwₙₜ _ (ev-init , ())

  disjoint-init/rf : Disjoint₁ EvInit (EvR ∪₁ EvF)
  disjoint-init/rf _ (ev-init , inj₁ ())
  disjoint-init/rf _ (ev-init , inj₂ ())
  
  disjoint-wₜ : Disjoint₁ (EvWₜ tmov) (EvWₜ trmw)
  disjoint-wₜ _ (ev-init refl , ev-init ())
  disjoint-wₜ _ (ev-w tmov≡tag₁ , ev-w trmw≡tag₂) =
    mov≢rmw (≡-trans tmov≡tag₁ (≡-sym trmw≡tag₂))

  disjoint-rₜ : Disjoint₁ (EvRₜ tmov) (EvRₜ trmw)
  disjoint-rₜ _ (ev-r tmov≡tag₁ , ev-r trmw≡tag₂) =
    mov≢rmw (≡-trans tmov≡tag₁ (≡-sym trmw≡tag₂))

  disjoint-rwₜ : Disjoint₁ (EvRWₜ tmov) (EvRWₜ trmw)
  disjoint-rwₜ x (x-mov , x-rmw) with rwₜ/rw x-mov | rwₜ/rw x-rmw
  ... | inj₁ x-r-mov | inj₁ x-r-rmw = disjoint-rₜ x (x-r-mov , x-r-rmw)
  ... | inj₁ x-r-mov | inj₂ x-w-rmw = disjoint-r/w x (rₜ⇒r x-r-mov , wₜ⇒w x-w-rmw)
  ... | inj₂ x-w-mov | inj₁ x-r-rmw = disjoint-r/w x (rₜ⇒r x-r-rmw , wₜ⇒w x-w-mov)
  ... | inj₂ x-w-mov | inj₂ x-w-rmw = disjoint-wₜ x (x-w-mov , x-w-rmw)

open ₁ public


module ₂ {arch₁ arch₂ : Arch} where

  import Burrow.Event.Core
  open import Burrow.Event.Pred
  open import Burrow.Event.Rel

  open Burrow.Event.Core {arch₁} renaming (Event to Event₁; event-init to event-init₁; event-skip to event-skip₁)
  open Burrow.Event.Core {arch₂} renaming (Event to Event₂; event-init to event-init₂; event-skip to event-skip₂)

  

  -- ### Operations - Subsititution: `Same` structures

  subst-suid :
      {x : Event₁} {y : Event₂}
    → SameUid x y
    → {uid : UniqueId}
    → HasUid uid x
      ----------------
    → HasUid uid y
  subst-suid (same-uid has-uid-init x-uid) has-uid-init = x-uid
  subst-suid (same-uid has-uid-skip x-uid) has-uid-skip = x-uid
  subst-suid (same-uid has-uid-r    x-uid) has-uid-r    = x-uid
  subst-suid (same-uid has-uid-w    x-uid) has-uid-w    = x-uid
  subst-suid (same-uid has-uid-f    x-uid) has-uid-f    = x-uid

  subst-stid :
      {x : Event₁} {y : Event₂}
    → SameTid x y
    → {tid : ThreadId}
    → HasTid tid x
      ----------------
    → HasTid tid y
  subst-stid (same-tid has-tid-skip x-tid) has-tid-skip = x-tid
  subst-stid (same-tid has-tid-r x-tid)    has-tid-r    = x-tid
  subst-stid (same-tid has-tid-w x-tid)    has-tid-w    = x-tid
  subst-stid (same-tid has-tid-f x-tid)    has-tid-f    = x-tid

  subst-sloc :
      {x : Event₁} {y : Event₂}
    → SameLoc x y
    → {loc : Location}
    → HasLoc loc x
      ----------------
    → HasLoc loc y
  subst-sloc (same-loc has-loc-init x-loc) has-loc-init = x-loc
  subst-sloc (same-loc has-loc-r    x-loc) has-loc-r    = x-loc
  subst-sloc (same-loc has-loc-w    x-loc) has-loc-w    = x-loc
  
  subst-sval :
      {x : Event₁} {y : Event₂}
    → SameVal x y
    → {val : Value}
    → HasVal val x
      -------------
    → HasVal val y
  subst-sval (same-val has-val-init x-val) has-val-init = x-val
  subst-sval (same-val has-val-r    x-val) has-val-r    = x-val
  subst-sval (same-val has-val-w    x-val) has-val-w    = x-val


  -- ## Properties: Excluded Middle

  stid-dec : DecRel (SameTid {arch₁} {arch₂})
  stid-dec x y with ev-init/tid x | ev-init/tid y
  stid-dec _ _ | xopt₁ ev-init _ | _ = no λ{(same-tid () _)}
  stid-dec _ _ | xopt₂ _       _ | xopt₁ ev-init ¬b = no λ{(same-tid _ ())}
  stid-dec x y | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) =
    case tid-dec≡ tid₁ tid₂ of
    λ{ (yes refl) → yes (same-tid x-tid₁ y-tid₂)
     ; (no tid₁≢tid₂) → no (λ{xy-stid → tid₁≢tid₂ (tid-unique (subst-stid xy-stid x-tid₁) y-tid₂)})
     }

  -- ## Properties: Symmetry

  -- Note that the default definitions of `Symmetric` and `Transitivity` are /not/ used; This is because
  -- the properties below need to work across different labels, which those default definitions disallow.

  sym-same-uid :
      {x : Event₁} {y : Event₂}
    → SameUid x y
      -----------
    → SameUid y x
  sym-same-uid (same-uid x y) = same-uid y x

  sym-same-tid :
      {x : Event₁} {y : Event₂}
    → SameTid x y
      -----------
    → SameTid y x
  sym-same-tid (same-tid x y) = same-tid y x

  sym-same-loc :
      {x : Event₁} {y : Event₂}
    → SameLoc x y
      -----------
    → SameLoc y x
  sym-same-loc (same-loc x y) = same-loc y x

  sym-same-val :
      {x : Event₁} {y : Event₂}
    → SameVal x y
      -----------
    → SameVal y x
  sym-same-val (same-val x y) = same-val y x

  private
    variable
      uid₁ uid₂ : UniqueId
      tid₁ tid₂ : ThreadId
      loc₁ loc₂ : Location
      val₁ val₂ : Value

  -- ## Operations: Coercion

  -- ### Operations - Coercion: Labels

  coerce-init-label :
      event-init₁ uid₁ loc₁ val₁ ≡ event-init₁ uid₂ loc₂ val₂
    → event-init₂ uid₁ loc₁ val₁ ≡ event-init₂ uid₂ loc₂ val₂
  coerce-init-label refl = refl

  coerce-skip-label :
      event-skip₁ uid₁ tid₁ ≡ event-skip₁ uid₂ tid₂
    → event-skip₂ uid₁ tid₁ ≡ event-skip₂ uid₂ tid₂
  coerce-skip-label refl = refl
  
open ₂ public


module ₃ {arch₁ arch₂ arch₃ : Arch} where

  open import Burrow.Event.Rel using (SameLoc; SameVal; SameTid)

  open SameLoc
  open SameVal
  open SameTid
  

  -- ## Properties: Transitivity

  -- | Transitivity of `SameLoc`
  trans-same-loc : 
    Trans (SameLoc {arch₁} {arch₂}) (SameLoc {arch₂} {arch₃}) (SameLoc {arch₁} {arch₃})
  trans-same-loc (same-loc x y₁) (same-loc y₂ z) = 
    same-loc x (subst-loc (≡-sym (loc-unique y₁ y₂)) z)

  -- Transitivity of `SameVal`
  trans-same-val : Trans (SameVal {arch₁} {arch₂}) (SameVal {arch₂} {arch₃}) (SameVal {arch₁} {arch₃})
  trans-same-val (same-val x y₁) (same-val y₂ z) =
    same-val x (subst-val (≡-sym (val-unique y₁ y₂)) z)

  -- Transitivity of `SameTid`
  trans-same-tid : Trans (SameTid {arch₁} {arch₂}) (SameTid {arch₂} {arch₃}) (SameTid {arch₁} {arch₃})
  trans-same-tid (same-tid x y₁) (same-tid y₂ z) =
    same-tid x (subst-tid (≡-sym (tid-unique y₁ y₂)) z)

open ₃ public


module ₄ {arch₁ arch₂ arch₃ arch₄ : Arch} where

  open import Burrow.Event.Rel using (SameLoc; SameVal; SameTid)


  -- Two-step transitivity of `SameLoc`
  trans-same-loc₂ :
    Trans₂ (SameLoc {arch₁} {arch₂}) (SameLoc {arch₂} {arch₃}) (SameLoc {arch₃} {arch₄}) (SameLoc {arch₁} {arch₄})
  trans-same-loc₂ x~y y~z z~w =
    trans-same-loc x~y (trans-same-loc y~z z~w)

  -- Two-step transitivity of `SameVal`
  trans-same-val₂ :
    Trans₂ (SameVal {arch₁} {arch₂}) (SameVal {arch₂} {arch₃}) (SameVal {arch₃} {arch₄}) (SameVal {arch₁} {arch₄})
  trans-same-val₂ x~y y~z z~w =
    trans-same-val x~y (trans-same-val y~z z~w)

  -- Two-step transitivity of `SameTid`
  trans-same-tid₂ :
      Trans₂ (SameTid {arch₁} {arch₂}) (SameTid {arch₂} {arch₃}) (SameTid {arch₃} {arch₄}) (SameTid {arch₁} {arch₄})
  trans-same-tid₂ x~y y~z z~w = trans-same-tid x~y (trans-same-tid y~z z~w)

open ₄ public
