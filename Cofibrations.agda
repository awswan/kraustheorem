{- We put the definition of cofibration in this file. -}
module Cofibrations where

{- Some basic propositions for type theory and two level type theory. -}
open import Agda.Primitive
open import Basics
open import StrictBasics


private variable
  ℓ ℓ' ℓ'' : Level

{- A map is a cofibration if it has the left lifting property against trivial
   fibrations, which is formulated in type theory as follows.

   In particular note that trivial fibrations appear as contractible types C,
   and that the "upper triangle" commutativity is given using strict equality. -}
isCof : {A : Set ℓ} {B : Set ℓ'} → (A → B) → {ℓ'' : Level} →
  SSet _
isCof {A = A} {B = B} m {ℓ'' = ℓ''} =
  (C : B → Set ℓ'') → ((b : B) → isContr (C b)) → (h : (a : A) → C (m a)) →
    Σˢ ((b : B) → C b) (λ c → (a : A) → (c (m a)) ≡ˢ (h a))
