{-# OPTIONS --without-K --safe #-}

module Burrow.Internal.Helpers where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level; _⊔_)
open import Function using (_∘_; _∘₂_)
open import Function.Nary.NonDependent using (congₙ; Injectiveₙ; _⇉_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]; fromInj₁; fromInj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL; IsEquivalence; Trans; Symmetric)
-- Local library imports
open import Dodo.Binary using (DecRel)


private
  variable
    a ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C D E F : Set a

-- # Binary Relations


-- | Two-step transitivity.
--
-- Intuitively: `(P ⨾ Q ⨾ R) x y → S x y`
Trans₂ : REL A B ℓ₁ → REL B C ℓ₂ → REL C D ℓ₃ → REL A D ℓ₄ → Set _
Trans₂ P Q R S = ∀ {i j k l} → P i j → Q j k → R k l → S i l


contrapositive : {a b : Level} {A : Set a} {B : Set b}
  → ( A → B )
    -------------
  → ( ¬ B → ¬ A )
contrapositive f ¬b a = ¬b (f a)


-- # Sum (_⊎_)

⊥⊎-elim :
    ( A → ⊥ )
  → ( B → C )
    ---------
  → A ⊎ B → C
⊥⊎-elim f g = [ (⊥-elim ∘ f) , g ]


⊎⊥-elim :
    ( A → C )
  → ( B → ⊥ )
    ---------
  → A ⊎ B → C
⊎⊥-elim f g = [ f , (⊥-elim ∘ g) ]

sumʳ :
    ¬ A
  → A ⊎ B
    -----
  → B
sumʳ ¬x = fromInj₂ (⊥-elim ∘ ¬x)


sumˡ :
    ¬ B
  → A ⊎ B
    -----
  → A
sumˡ ¬y = fromInj₁ (⊥-elim ∘ ¬y)



-- # Equality


≢-sym : {x y : A}
  → x ≢ y
    -----
  → y ≢ x
≢-sym x≢y refl = x≢y refl


≡-equivalence : IsEquivalence {_} {_} {A} _≡_
≡-equivalence =
  record
    { refl   =  refl
    ; sym    =  ≡-sym
    ; trans  =  ≡-trans
    }


cong-dec≡ :
    (f : A → C)
  → (∀ {x y : A} → f x ≡ f y → x ≡ y)
  → {x y : A}
  → Dec (x ≡ y)
    -------------------
  → Dec (f x ≡ f y)
cong-dec≡ _ _ (yes refl) = yes refl
cong-dec≡ _ f (no x≢y)   = no (x≢y ∘ f)


cong₂-dec≡ :
    (f : A → B → C)
  → (∀ {x y : A} {w z : B} → f x w ≡ f y z → x ≡ y)
  → (∀ {x y : A} {w z : B} → f x w ≡ f y z → w ≡ z)
  → {x y : A}
  → {w z : B}
  → Dec (x ≡ y)
  → Dec (w ≡ z)
    -------------------
  → Dec (f x w ≡ f y z)
cong₂-dec≡ _ _ _ (yes refl) (yes refl) = yes refl
cong₂-dec≡ _ _ f (yes refl) (no w≢z)   = no (w≢z ∘ f)
cong₂-dec≡ _ f _ (no x≢y)   _          = no (x≢y ∘ f)


cong₃-dec≡ :
    (f : A → B → C → D)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} → f x₁ x₂ x₃ ≡ f y₁ y₂ y₃ → x₁ ≡ y₁)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} → f x₁ x₂ x₃ ≡ f y₁ y₂ y₃ → x₂ ≡ y₂)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} → f x₁ x₂ x₃ ≡ f y₁ y₂ y₃ → x₃ ≡ y₃)
  → {x₁ y₁ : A}
  → {x₂ y₂ : B}
  → {x₃ y₃ : C}
  → Dec (x₁ ≡ y₁)
  → Dec (x₂ ≡ y₂)
  → Dec (x₃ ≡ y₃)
    -----------------------
  → Dec (f x₁ x₂ x₃ ≡ f y₁ y₂ y₃)
cong₃-dec≡ _ _ _ _ (yes refl) (yes refl) (yes refl) = yes refl
cong₃-dec≡ _ _ _ f (yes refl) (yes refl) (no p≢q)   = no (p≢q ∘ f)
cong₃-dec≡ _ _ f _ (yes refl) (no w≢z)   _          = no (w≢z ∘ f)
cong₃-dec≡ _ f _ _ (no x≢y)   _          _          = no (x≢y ∘ f)

cong₄-dec :
    (f : A → B → C → D → E)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} → f x₁ x₂ x₃ x₄ ≡ f y₁ y₂ y₃ y₄ → x₁ ≡ y₁)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} → f x₁ x₂ x₃ x₄ ≡ f y₁ y₂ y₃ y₄ → x₂ ≡ y₂)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} → f x₁ x₂ x₃ x₄ ≡ f y₁ y₂ y₃ y₄ → x₃ ≡ y₃)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} → f x₁ x₂ x₃ x₄ ≡ f y₁ y₂ y₃ y₄ → x₄ ≡ y₄)
  → {x₁ y₁ : A}
  → {x₂ y₂ : B}
  → {x₃ y₃ : C}
  → {x₄ y₄ : D}
  → Dec (x₁ ≡ y₁)
  → Dec (x₂ ≡ y₂)
  → Dec (x₃ ≡ y₃)
  → Dec (x₄ ≡ y₄)
    -----------------------
  → Dec (f x₁ x₂ x₃ x₄ ≡ f y₁ y₂ y₃ y₄)
cong₄-dec _ _ _ _ _ (yes refl) (yes refl) (yes refl) (yes refl) = yes refl
cong₄-dec _ _ _ _ f (yes refl) (yes refl) (yes refl) (no x≢y)   = no (x≢y ∘ f)
cong₄-dec _ _ _ f _ (yes refl) (yes refl) (no x≢y)   _          = no (x≢y ∘ f)
cong₄-dec _ _ f _ _ (yes refl) (no x≢y)   _          _          = no (x≢y ∘ f)
cong₄-dec _ f _ _ _ (no x≢y)   _          _          _          = no (x≢y ∘ f)

cong₅-dec≡ :
    (f : A → B → C → D → E → F)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} {x₅ y₅ : E} → f x₁ x₂ x₃ x₄ x₅ ≡ f y₁ y₂ y₃ y₄ y₅ → x₁ ≡ y₁)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} {x₅ y₅ : E} → f x₁ x₂ x₃ x₄ x₅ ≡ f y₁ y₂ y₃ y₄ y₅ → x₂ ≡ y₂)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} {x₅ y₅ : E} → f x₁ x₂ x₃ x₄ x₅ ≡ f y₁ y₂ y₃ y₄ y₅ → x₃ ≡ y₃)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} {x₅ y₅ : E} → f x₁ x₂ x₃ x₄ x₅ ≡ f y₁ y₂ y₃ y₄ y₅ → x₄ ≡ y₄)
  → (∀ {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C} {x₄ y₄ : D} {x₅ y₅ : E} → f x₁ x₂ x₃ x₄ x₅ ≡ f y₁ y₂ y₃ y₄ y₅ → x₅ ≡ y₅)
  → {x₁ y₁ : A}
  → {x₂ y₂ : B}
  → {x₃ y₃ : C}
  → {x₄ y₄ : D}
  → {x₅ y₅ : E}
  → Dec (x₁ ≡ y₁)
  → Dec (x₂ ≡ y₂)
  → Dec (x₃ ≡ y₃)
  → Dec (x₄ ≡ y₄)
  → Dec (x₅ ≡ y₅)
    -----------------------
  → Dec (f x₁ x₂ x₃ x₄ x₅ ≡ f y₁ y₂ y₃ y₄ y₅)
cong₅-dec≡ _ _ _ _ _ _ (yes refl) (yes refl) (yes refl) (yes refl) (yes refl) = yes refl
cong₅-dec≡ _ _ _ _ _ f (yes refl) (yes refl) (yes refl) (yes refl) (no x≢y)   = no (x≢y ∘ f)
cong₅-dec≡ _ _ _ _ f _ (yes refl) (yes refl) (yes refl) (no x≢y)   _          = no (x≢y ∘ f)
cong₅-dec≡ _ _ _ f _ _ (yes refl) (yes refl) (no x≢y)   _          _          = no (x≢y ∘ f)
cong₅-dec≡ _ _ f _ _ _ (yes refl) (no x≢y)   _          _          _          = no (x≢y ∘ f)
cong₅-dec≡ _ f _ _ _ _ (no x≢y)   _          _          _          _          = no (x≢y ∘ f)


-- # Decidable

Dec≡ : Set → Set
Dec≡ A = DecRel (_≡_ {_} {A})

ℕ-dec≡ : Dec≡ ℕ
ℕ-dec≡ zero    zero    = yes refl
ℕ-dec≡ (suc x) (suc y) = cong-suc (ℕ-dec≡ x y)
  where
  cong-suc : ∀ {x y : ℕ} → Dec (x ≡ y) → Dec (suc x ≡ suc y)
  cong-suc (yes x≡y) = yes (cong suc x≡y)
  cong-suc (no  x≢y) = no λ{refl → x≢y refl}
ℕ-dec≡ zero    (suc _) = no (λ ())
ℕ-dec≡ (suc _) zero    = no (λ ())


×-dec :
    Dec A
  → Dec B
    -----------
  → Dec (A × B)
×-dec (yes a) (yes b) = yes (a , b)
×-dec (yes a) (no ¬b) = no (¬b ∘ proj₂)
×-dec (no ¬a) _       = no (¬a ∘ proj₁)


-- # Type-checking helpers


data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x


-- | When matching on a variable, we may need to remember it is equal.
inspect : (x : A) → Singleton x
inspect x = x with≡ refl


-- | Pattern-matching on a constructor is often clumsy. This function makes it
-- more convenient.
--
-- # Example
--
-- ```
-- case x of
-- λ{ inj₁ x → ?
--  ; inj₂ y → ?
--  }
-- ```
case_of_ :
    A
  → (A → B)
    -------
  → B
case x of f = f x


-- | Allows pattern-matching simultaneously on two values.
--
-- See also `case_of_`.
case₂_and_of_ :
    A
  → B
  → (A → B → C)
    -----------
  → C
case₂ x and y of f = f x y
