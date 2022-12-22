{-# OPTIONS --cubical #-}

{- This file contains a couple of examples of cofibrations from the Cubical Agda library.
   More generally, any point constructor of a HIT is a cofibration. -}

{- For just this file we will use the Cubical Agda library. -}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Truncation renaming (elim to truncElim)
open import Cubical.HITs.SetQuotients renaming (elim to quotElim)
open import Cubical.Data.Nat hiding (elim)

{- We use strict equality to formulate the definition of cofibration. -}
open import StrictBasics

module CofibrationExamples where

private variable
  ℓ ℓ' ℓ'' : Level


{- The definition of cofibration. We copy this from Cofibrations rather than import so
   we can use the standard Cubical defintion of isContr, allowing us to make better use
   of the library. Technically this is a different definition, since it uses path types
   rather than Id types, but it turns out not to make much difference here. -}
isCof : {A : Set ℓ} {B : Set ℓ'} → (A → B) → {ℓ'' : Level} →
  SSet _
isCof {A = A} {B = B} m {ℓ'' = ℓ''} =
  (C : B → Set ℓ'') → ((b : B) → isContr (C b)) → (h : (a : A) → C (m a)) →
    Σˢ ((b : B) → C b) (λ c → (a : A) → (c (m a)) ≡ˢ (h a))

{- We first show that truncation maps are cofibration for any truncation level.
   As a special case, this includes -1 truncation. -}
∣∣Cof : (A : Type ℓ) (n : ℕ) → isCof (∣_∣ₕ {A = A} {n = suc n}) {ℓ'' = ℓ'}
∣∣Cof A n C CContr h = record { fst = f ; snd = λ a → reflˢ }
  where
    f : (x : ∥ A ∥ (suc n)) → C x
    f = truncElim (λ z → isContr→isOfHLevel (suc n) (CContr z)) h

{- The definition of -2 truncation in the Cubical library does not satisfy the
   right computation rule to give a fibration, so we define our own version by hand. -}
data ∥_∥₋₂ (A : Type ℓ) : Type ℓ where
  ∣_∣₋₂ : A → ∥ A ∥₋₂
  centre : ∥ A ∥₋₂
  path : (z : ∥ A ∥₋₂) → z ≡ centre

{- Even -2 truncation is a cofibration. -}
∣∣₋₂Cof : (A : Type ℓ) → isCof (∣_∣₋₂ {A = A}) {ℓ'' = ℓ'}
∣∣₋₂Cof A C CContr h = record { fst = f ; snd = λ _ → reflˢ }
  where
    f : (x  : ∥ A ∥₋₂) → C x
    f ∣ a ∣₋₂ = h a
    f centre = fst (CContr centre)
    f (path x i) = toPathP {A = λ i → C (path x i)}
                           (isContr→isProp (CContr centre) (transport (cong C (path x)) (f x))
                                                           (fst (CContr centre))) i

{- Set quotient maps are also cofibrations. -}
setQuotCof : (A : Type ℓ) (R : A → A → Type ℓ') → isCof ([_] {A = A} {R = R}) {ℓ'' = ℓ''}
setQuotCof A R C CContr h = record { fst = f ; snd = λ _ → reflˢ }
  where
    f : (x : A / R) → C x
    f = quotElim (λ x → isContr→isOfHLevel 2 (CContr x)) h
                 λ a b r → toPathP (isContr→isProp (CContr _) _ _)
