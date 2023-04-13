{-# OPTIONS --safe #-}

-- Stdlib imports
open import Relation.Unary using (_∈_)
-- Local imports
open import Burrow.Primitives using (Arch)
open import Burrow.Execution.Core using (Execution)
open import Burrow.Event.Core using (Event)
open import Burrow.WellFormed.Core using (WellFormed)

open Execution


-- | Mostly type aliases and combinators for mapping proofs
module Burrow.Framework.Primitives
  {archˢ archᵗ : Arch}
  {dst : Execution {archᵗ}}
  (dst-wf : WellFormed dst)
  (ev[⇐] : {x : Event {archᵗ}} → (x∈dst : x ∈ events dst) → Event {archˢ})
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; cong) renaming (sym to ≡-sym)
open import Function using (_∘_; flip)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architecture Definitions
open import Burrow.WellFormed.Derived dst-wf


--
-- # Notations
--
-- We use the following notations:
-- * [⇒]  - source-to-target mapping, defined in terms of source events
-- * [⇐]  - target-to-source mapping, defined in terms of target events
-- * [$⇒] - source-to-target mapping, defined in terms of target events
-- * [⇐$] - target-to-source mapping, defined in terms of source events
--
-- Examples:
-- * P[⇒]  : P x → P (ev[⇒] x∈src)
-- * P[⇐]  : P x → P (ev[⇐] x∈dst)
-- * P[$⇒] : P (ev[⇐] x∈dst) → P x
-- * P[⇐$] : P (ev[⇒] x∈src) → P x
--
-- The `[$⇒]/[⇐$]` definitions may seem somewhat clumsy, but are often useful.
-- For instance, `[⇐]` and `[$⇒]` are defined in terms of the /target/, from
-- which the /source/ is derived. Their corresponding `[⇐$]` and `[⇒]` mappings
-- can easily be derived (e.g., see `[⇐]→₁[⇐$]`).
--


-- # Aliasses

private
  Eventˢ = Event {archˢ}
  Eventᵗ = Event {archᵗ}

  Predˢ = Pred₀ Eventˢ
  Predᵗ = Pred₀ Eventᵗ

  Relˢ = Rel₀ Eventˢ
  Relᵗ = Rel₀ Eventᵗ

  variable
    xˢ : Eventˢ
    xᵗ : Eventᵗ
    Pˢ : Predˢ
    Pᵗ : Predᵗ
    Rˢ Qˢ : Relˢ
    Rᵗ Qᵗ : Relᵗ


-- # Execution

src-events : Predˢ
src-events x-src = ∃[ x-dst ] ∃[ x∈dst ] (x-src ≡ ev[⇐] {x-dst} x∈dst)


-- | Many relations are verbatim mapped to the source. This function generalizes over that.
--
-- # Use Cases
--
-- Though, /which/ relations are mapped verbatim differs per proof.
-- * `po`      - for mapping and elimination proofs (but not reorder)
-- * `rf`/`co` - for mapping and reorder proofs (but not elimination)
-- * `rmw`     - for any proof
src-rel :
    Rᵗ ˡ∈ex -- ∈ events dst
  → Rᵗ ʳ∈ex -- ∈ events dst
  → Relˢ
src-rel Rˡ∈dst Rʳ∈dst x-src y-src =
  ∃[ x-dst ] ∃[ y-dst ] ∃[ dst-rmw[xy] ]
    let x∈dst = Rˡ∈dst dst-rmw[xy]
        y∈dst = Rʳ∈dst dst-rmw[xy]
    in (x-src ≡ ev[⇐] {x-dst} x∈dst × y-src ≡ ev[⇐] {y-dst} y∈dst)


src-rmw : Relˢ
src-rmw = src-rel rmwˡ∈ex rmwʳ∈ex


-- # Event Mappings

-- | Maps a source event to its corresponding event in the target
--
-- Note that this requires a /proof that the event is in the source/.
ev[⇒] :
    xˢ ∈ src-events
    ----------------
  → Eventᵗ
ev[⇒] = proj₁


events[⇒] :
    (x∈src : xˢ ∈ src-events)
    --------------------------
  → (ev[⇒] x∈src) ∈ events dst
events[⇒] (_ , x∈dst , _) = x∈dst


events[⇐] :
    (x∈dst : xᵗ ∈ events dst)
    --------------------------
  → (ev[⇐] x∈dst) ∈ src-events
events[⇐] {x} x∈dst = (x , x∈dst , refl)


-- | Starting with event `x` in the source: Mapping `x` to the target,
-- then mapping the result to the source, gives `x` again.
ev[⇒⇐] :
    (x∈src : xˢ ∈ src-events)
    ---------------------------
  → xˢ ≡ ev[⇐] (events[⇒] x∈src)
ev[⇒⇐] {x-src} (x-dst , x∈dst , refl) = refl


-- # Type Aliases

-- | Inhabitants of `Pred[⇒]² Pˢ Pᵗ` prove that `Pˢ` transforms to `Pᵗ` along `ev[⇒]`
Pred[⇒] : REL₀ Predˢ Predᵗ
Pred[⇒] Pˢ Pᵗ =
  ∀ {xˢ}
  → (x∈src : xˢ ∈ src-events)
  → Pˢ xˢ
    ------------------------
  → Pᵗ (ev[⇒] x∈src)

Pred[⇐$] : REL₀ Predˢ Predᵗ
Pred[⇐$] Pˢ Pᵗ =
  ∀ {xˢ}
  → (x∈src : xˢ ∈ src-events)
  → Pᵗ (ev[⇒] x∈src)
    ------------------------
  → Pˢ xˢ

Pred[$⇒] : REL₀ Predˢ Predᵗ
Pred[$⇒] Pˢ Pᵗ =
  ∀ {xᵗ}
  → (x∈dst : xᵗ ∈ events dst)
  → Pˢ (ev[⇐] x∈dst)
    ------------------------
  → Pᵗ xᵗ

Pred[⇐] : REL₀ Predˢ Predᵗ
Pred[⇐] Pˢ Pᵗ =
  ∀ {xᵗ}
  → (x∈dst : xᵗ ∈ events dst)
  → Pᵗ xᵗ
    ------------------------
  → Pˢ (ev[⇐] x∈dst)


-- | Inhabitants of `Pred[⇒] P` prove that `P` remains along `ev[⇒]`
Pred[⇒]² : Pred₀ (∀ {arch : Arch} → Pred₀ (Event {arch}))
Pred[⇒]² P = Pred[⇒] P P

-- | Inhabitants of `Pred[⇐$]² P` prove that `P` remains along `ev[⇐$]`
Pred[⇐$]² : Pred₀ (∀ {arch : Arch} → Pred₀ (Event {arch}))
Pred[⇐$]² P = Pred[⇐$] P P
  
-- | Inhabitants of `Pred[$⇒]² P` prove that `P` remains along `ev[$⇒]`
Pred[$⇒]² : Pred₀ (∀ {arch : Arch} → Pred₀ (Event {arch}))
Pred[$⇒]² P = Pred[$⇒] P P
  
-- | Inhabitants of `Pred[⇐]² P` prove that `P` remains along `ev[⇐]`
Pred[⇐]² : (∀ {arch : Arch} → Pred₀ (Event {arch})) → Set
Pred[⇐]² P = Pred[⇐] P P


Rel[⇒] : REL₀ Relˢ Relᵗ
Rel[⇒] Rˢ Rᵗ =
  ∀ {xˢ yˢ}
  → (x∈src : xˢ ∈ src-events)
  → (y∈src : yˢ ∈ src-events)
  → Rˢ xˢ yˢ
    ------------------------------
  → Rᵗ (ev[⇒] x∈src) (ev[⇒] y∈src)

Rel[⇐$] : REL₀ Relˢ Relᵗ
Rel[⇐$] Rˢ Rᵗ =
  ∀ {xˢ yˢ}
  → (x∈src : xˢ ∈ src-events)
  → (y∈src : yˢ ∈ src-events)
  → Rᵗ (ev[⇒] x∈src) (ev[⇒] y∈src)
    ------------------------------
  → Rˢ xˢ yˢ

Rel[$⇒] : REL₀ Relˢ Relᵗ
Rel[$⇒] Rˢ Rᵗ =
  ∀ {xᵗ yᵗ}
  → (x∈dst : xᵗ ∈ events dst)
  → (y∈dst : yᵗ ∈ events dst)
  → Rˢ (ev[⇐] x∈dst) (ev[⇐] y∈dst)
    ------------------------------
  → Rᵗ xᵗ yᵗ

Rel[⇐] : REL₀ Relˢ Relᵗ
Rel[⇐] Rˢ Rᵗ =
  ∀ {xᵗ yᵗ}
  → (x∈dst : xᵗ ∈ events dst)
  → (y∈dst : yᵗ ∈ events dst)
  → Rᵗ xᵗ yᵗ
    ------------------------------
  → Rˢ (ev[⇐] x∈dst) (ev[⇐] y∈dst)

Rel[⇒]² : Pred₀ (∀ {arch : Arch} → Rel₀ (Event {arch}))
Rel[⇒]² R = Rel[⇒] R R

Rel[⇐$]² : Pred₀ (∀ {arch : Arch} → Rel₀ (Event {arch}))
Rel[⇐$]² R = Rel[⇐$] R R

Rel[$⇒]² : Pred₀ (∀ {arch : Arch} → Rel₀ (Event {arch}))
Rel[$⇒]² R = Rel[$⇒] R R

Rel[⇐]² : Pred₀ (∀ {arch : Arch} → Rel₀ (Event {arch}))
Rel[⇐]² R = Rel[⇐] R R


-- # Mapping Combinators

[$⇒]→₁[⇒] :
    Pred[$⇒] Pˢ Pᵗ
    --------------
  → Pred[⇒] Pˢ Pᵗ
[$⇒]→₁[⇒] {Pˢ} P[$⇒] x∈src Pxˢ =
  let x∈dst = events[⇒] x∈src
  in P[$⇒] x∈dst (subst Pˢ (ev[⇒⇐] x∈src) Pxˢ)

[⇐]→₁[⇐$] :
    Pred[⇐] Pˢ Pᵗ
    --------------
  → Pred[⇐$] Pˢ Pᵗ
[⇐]→₁[⇐$] {Pˢ} P[⇐] x∈src Pxᵗ =
  let x∈dst = events[⇒] x∈src
  in subst Pˢ (≡-sym (ev[⇒⇐] x∈src)) (P[⇐] x∈dst Pxᵗ)

[⇐$]→₁[⇐] :
    Pred[⇐$] Pˢ Pᵗ
    --------------
  → Pred[⇐] Pˢ Pᵗ
[⇐$]→₁[⇐] P[⇐$] = P[⇐$] ∘ events[⇐]


[$⇒]→₂[⇒] :
    Rel[$⇒] Rˢ Rᵗ
    -------------
  → Rel[⇒] Rˢ Rᵗ
[$⇒]→₂[⇒] {Rˢ} {Rᵗ} R[$⇒] x∈src y∈src Rxyˢ =
  let x∈dst = events[⇒] x∈src
      y∈dst = events[⇒] y∈src
  in R[$⇒] x∈dst y∈dst (subst-rel Rˢ (ev[⇒⇐] x∈src) (ev[⇒⇐] y∈src) Rxyˢ)

[⇐]→₂[⇐$] :
    Rel[⇐] Rˢ Rᵗ
    -------------
  → Rel[⇐$] Rˢ Rᵗ
[⇐]→₂[⇐$] {Rˢ} {Rᵗ} R[⇐] x∈src y∈src Rxyᵗ =
  let x∈dst = events[⇒] x∈src
      y∈dst = events[⇒] y∈src
  in subst-rel Rˢ (≡-sym (ev[⇒⇐] x∈src)) (≡-sym (ev[⇒⇐] y∈src)) (R[⇐] x∈dst y∈dst Rxyᵗ)

[⇐$]→₂[⇐] :
    Rel[⇐$] Rˢ Rᵗ
    -------------
  → Rel[⇐] Rˢ Rᵗ
[⇐$]→₂[⇐] R[⇐$] x∈dst y∈dst =
  R[⇐$] (events[⇐] x∈dst) (events[⇐] y∈dst)

[⇒]→₂[$⇒] :
    Rel[⇒] Rˢ Rᵗ
    -------------
  → Rel[$⇒] Rˢ Rᵗ
[⇒]→₂[$⇒] R[⇒] x∈dst y∈dst =
  R[⇒] (events[⇐] x∈dst) (events[⇐] y∈dst)


¬₁[⇒] :
    Pred[⇐$] Pˢ Pᵗ
    -----------------------
  → Pred[⇒] (¬₁ Pˢ) (¬₁ Pᵗ)
¬₁[⇒] P[⇐$] = contraposition ∘ P[⇐$]

¬₁[⇐$] :
    Pred[⇒] Pˢ Pᵗ
    ----------------------
  → Pred[⇐$] (¬₁ Pˢ) (¬₁ Pᵗ)
¬₁[⇐$] P[⇒] = contraposition ∘ P[⇒]


¬₂[⇒] :
    Rel[⇐$] Rˢ Rᵗ
    ----------------------
  → Rel[⇒] (¬₂ Rˢ) (¬₂ Rᵗ)
¬₂[⇒] R[⇐$] x∈src y∈src = contraposition (R[⇐$] x∈src y∈src)


∩₂[⇒] :
    Rel[⇒] Rˢ Rᵗ
  → Rel[⇒] Qˢ Qᵗ
    ----------------------------
  → Rel[⇒] (Rˢ ∩₂ Qˢ) (Rᵗ ∩₂ Qᵗ)
∩₂[⇒] R[⇒] Q[⇒] x∈src y∈src (Rˢxy , Qˢxy) =
  (R[⇒] x∈src y∈src Rˢxy , Q[⇒] x∈src y∈src Qˢxy)

∪₂[⇒] :
    Rel[⇒] Rˢ Rᵗ
  → Rel[⇒] Qˢ Qᵗ
    ----------------------------
  → Rel[⇒] (Rˢ ∪₂ Qˢ) (Rᵗ ∪₂ Qᵗ)
∪₂[⇒] R[⇒] Q[⇒] x∈src y∈src =
  Data.Sum.map (R[⇒] x∈src y∈src) (Q[⇒] x∈src y∈src)

∪₂[⇐$] :
    Rel[⇐$] Rˢ Rᵗ
  → Rel[⇐$] Qˢ Qᵗ
    ----------------------------
  → Rel[⇐$] (Rˢ ∪₂ Qˢ) (Rᵗ ∪₂ Qᵗ)
∪₂[⇐$] R[⇐$] Q[⇐$] x∈src y∈src =
  Data.Sum.map (R[⇐$] x∈src y∈src) (Q[⇐$] x∈src y∈src)
  

--
-- We *explicitly* include the source and target relations, because Agda can't
-- always infer them.
dom[⇐] : (R : Relˢ) (Q : Relᵗ)
  → (∀ {x} → x ∈ codom Q → x ∈ events dst)
  → Rel[⇐] R Q
    -----------------------
  → Pred[⇐] (dom R) (dom Q)
dom[⇐] R Q Qʳ∈dst R[⇐]Q {x} x∈dst (y , Qxy) =
  let y∈dst = Qʳ∈dst (take-codom Q Qxy)
  in take-dom R (R[⇐]Q x∈dst y∈dst Qxy)

--
-- We *explicitly* include the source and target relations, because Agda can't
-- always infer them.
codom[⇐] : (R : Relˢ) (Q : Relᵗ)
  → (∀ {x} → x ∈ dom Q → x ∈ events dst)
  → Rel[⇐] R Q
    ---------------------------
  → Pred[⇐] (codom R) (codom Q)
codom[⇐] R Q Qˡ∈dst R[⇐]Q {y} y∈dst (x , Qxy) =
  let x∈dst = Qˡ∈dst (take-dom Q Qxy)
  in take-codom R (R[⇐]Q x∈dst y∈dst Qxy)

udr[⇐] : (R : Relˢ) (Q : Relᵗ)
  → (∀ {x} → x ∈ udr Q → x ∈ events dst)
  → Rel[⇐] R Q
    -----------------------
  → Pred[⇐] (udr R) (udr Q)
udr[⇐] R Q udrQ∈dst R[⇐]Q {x} x∈dst (inj₁ x∈Qˡ) =
  inj₁ (dom[⇐] R Q (udrQ∈dst ∘ inj₂) R[⇐]Q x∈dst x∈Qˡ)
udr[⇐] R Q udrQ∈dst R[⇐]Q {y} y∈dst (inj₂ y∈Qˡ) =
  inj₂ (codom[⇐] R Q (udrQ∈dst ∘ inj₁) R[⇐]Q y∈dst y∈Qˡ)

_ˡ∈src : Relˢ → Set
_ˡ∈src R =
  ∀ {x y}
  → R x y
    --------------
  → x ∈ src-events

_ʳ∈src : Relˢ → Set
_ʳ∈src R =
  ∀ {x y}
  → R x y
    --------------
  → y ∈ src-events

udr[_]∈src : Relˢ → Set
udr[_]∈src R =
  ∀ {x}
  → x ∈ udr R
    ---------------
  → x ∈ src-events

lr→udr : (R : Relˢ)
  → R ˡ∈src
  → R ʳ∈src
    ------------------
  → udr[ R ]∈src
lr→udr _ Rˡ∈src Rʳ∈src (inj₁ (_ , po[xy])) = Rˡ∈src po[xy]
lr→udr _ Rˡ∈src Rʳ∈src (inj₂ (_ , po[yx])) = Rʳ∈src po[yx]

-- |
--
-- Note that `R[⇒]Q : Rel[⇒] Rˢ Qᵗ` requires a proof that, for `Rˢ xˢ yˢ`, both
-- `xˢ` and `yˢ` are in `src`. We thus need the `Rˡ∈src : Rˢ ˡ∈src` to infer this.
⁺[⇒]ˡ :
    Rˢ ˡ∈src
  → Rel[⇒] Rˢ Qᵗ
    ------------------------------------------
  → Rel[⇒] (TransClosure Rˢ) (TransClosure Qᵗ)
⁺[⇒]ˡ Rˡ∈src R[⇒]Q x∈src y∈src [ Rxy ] = [ R[⇒]Q x∈src y∈src Rxy ]
⁺[⇒]ˡ Rˡ∈src R[⇒]Q x∈src y∈src ( Rxz ∷ R⁺zy ) =
  let z∈src = ⁺-lift-predˡ Rˡ∈src R⁺zy
  in R[⇒]Q x∈src z∈src Rxz ∷ ⁺[⇒]ˡ Rˡ∈src R[⇒]Q z∈src y∈src R⁺zy

⁺[⇐]ˡ :
    Qᵗ ˡ∈ex
  → Rel[⇐] Rˢ Qᵗ
    ----------------------------------------
  → Rel[⇐] (TransClosure Rˢ) (TransClosure Qᵗ)
⁺[⇐]ˡ Qˡ∈src R[⇐]Q x∈dst y∈dst [ Qxy ] = [ R[⇐]Q x∈dst y∈dst Qxy ]
⁺[⇐]ˡ Qˡ∈src R[⇐]Q x∈dst y∈dst ( Qxz ∷ Q⁺zy ) =
  let z∈dst = ⁺-lift-predˡ Qˡ∈src Q⁺zy
  in R[⇐]Q x∈dst z∈dst Qxz ∷ ⁺[⇐]ˡ Qˡ∈src R[⇐]Q z∈dst y∈dst Q⁺zy

imm[$⇒]ˡ :
      Qᵗ ˡ∈ex
    → Rel[⇐] Rˢ Qᵗ
    → Rel[$⇒] Rˢ Qᵗ
      -------------------------------------
    → Rel[$⇒] (immediate Rˢ) (immediate Qᵗ)
imm[$⇒]ˡ {Qᵗ} Qˡ∈dst R[⇐]Q R[$⇒]Q {x} {y} x∈dst y∈dst (Rxy , ¬∃z) =
  (R[$⇒]Q x∈dst y∈dst Rxy , ¬∃z')
  where
  ¬∃z' : ¬ (∃[ z ] Qᵗ x z × TransClosure Qᵗ z y)
  ¬∃z' (z , Qxz , Q⁺zy) =
    let z∈dst = ⁺-lift-predˡ Qˡ∈dst Q⁺zy
    in ¬∃z (ev[⇐] z∈dst , R[⇐]Q x∈dst z∈dst Qxz , ⁺[⇐]ˡ Qˡ∈dst R[⇐]Q z∈dst y∈dst Q⁺zy)

imm[⇐$]ˡ :
    Rˢ ˡ∈src
  → Rel[⇒] Rˢ Qᵗ
  → Rel[⇐$] Rˢ Qᵗ
    -------------------------------------
  → Rel[⇐$] (immediate Rˢ) (immediate Qᵗ)
imm[⇐$]ˡ {R} {Q} Rˡ∈src R[⇒]Q R[⇐$]Q {x} {y} x∈src y∈src (Qxy , ¬∃z) =
  R[⇐$]Q x∈src y∈src Qxy , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] R x z × TransClosure R z y)
  ¬∃z' (z , Rxz , R⁺zy) =
    let z∈src = ⁺-lift-predˡ Rˡ∈src R⁺zy
    in ¬∃z (ev[⇒] z∈src , R[⇒]Q x∈src z∈src Rxz , ⁺[⇒]ˡ Rˡ∈src R[⇒]Q z∈src y∈src R⁺zy)


relˡ∈src :
    (Rˡ∈dst : Rᵗ ˡ∈ex)
  → (Rʳ∈dst : Rᵗ ʳ∈ex)
    -----------------------------
  → (src-rel Rˡ∈dst Rʳ∈dst) ˡ∈src
relˡ∈src Rˡ∈dst _ (x-dst , _ , dst-R[xy] , refl , refl) =
  (x-dst , Rˡ∈dst dst-R[xy] , refl)

relʳ∈src :
    (Rˡ∈dst : Rᵗ ˡ∈ex)
  → (Rʳ∈dst : Rᵗ ʳ∈ex)
    -----------------------------
  → (src-rel Rˡ∈dst Rʳ∈dst) ʳ∈src
relʳ∈src _ Rʳ∈dst (x-dst , y-dst , dst-R[xy] , refl , refl) =
  (y-dst , Rʳ∈dst dst-R[xy] , refl)


rmwˡ∈src : src-rmw ˡ∈src
rmwˡ∈src = relˡ∈src rmwˡ∈ex rmwʳ∈ex

rmwʳ∈src : src-rmw ʳ∈src
rmwʳ∈src = relʳ∈src rmwˡ∈ex rmwʳ∈ex

udr-rmw∈src : udr[ src-rmw ]∈src
udr-rmw∈src = lr→udr src-rmw rmwˡ∈src rmwʳ∈src
