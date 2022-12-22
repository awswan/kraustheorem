open import Agda.Primitive

open import Basics
open import StrictBasics
open import Cofibrations

module KrausTheorem where

private variable
  ℓ ℓ' ℓ'' : Level

{- Strictify a factorisation. Compare this to the original version due to Escardó at
  https://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html.
  We can recover the original as a special case by noting that truncation maps are
  cofibrations. -}
module StrictifyFactorisation (A : Set ℓ) (B : Set ℓ') (C : Set ℓ'') (m : A → B)
  (mCof : isCof m) -- m is a cofibration
  (f : B → C)
  (g : A → C)
  (comm : (a : A) → f (m a) ≡ g a) -- f ∘ m = g up to propositional equality
  where

  {- Diagonal filler for a lifting problem that we need. -}
  filler : Σˢ ((b : B) →
    Σ C (λ c → f b ≡ c))
      (λ f'comm → (a : A) → f'comm (m a) ≡ˢ (g a , comm a))
  filler = mCof (λ b → Σ C (λ c → f b ≡ c)) (λ b → isContrSingl (f b))
                λ a → (g a) , (comm a)

  {- We use the diagonal filler to both find f' and show the factorisation strictly commutes. -}
  f' : B → C
  f' b = Σ.fst (Σˢ.fst filler b)

  comm' : (a : A) → f' (m a) ≡ˢ g a
  comm' a = congˢ Σ.fst (Σˢ.snd filler a)

{- We define a type A to be transitive if (A , a) and (A , a') are equal as pointed
   types for any a, a' in A. Note that univalence implies any set with
   decidable equality is transitive. -}
isTransitive : Set → Set₁
isTransitive A = (a a' : A) → (A , a) ≡ _,_ {A = Set} {B = λ A → A} A a'

{- We use this to construct the inverse to m. -}
module Invert (A B : Set) (m : A → B) (mCof : isCof m) -- let m be a cofibration
  (a₀ : A) (Atrans : isTransitive A) -- and let A be transitivex
  where

  {- We first define the factorisation that we're going to strictify. -}
  f : B → Set•
  f b = A , a₀

  g : A → Set•
  g a = (A , a)

  comm : (a : A) → f (m a) ≡ g a
  comm a = Atrans a₀ a

  {- Now we can strictify to get f' making a strictly commutative triangle. -}
  open StrictifyFactorisation A B Set• m mCof f g comm

  {- The type component. -}
  A' : B → Set
  A' b = Σ.fst (f' b)

  {- If we feed m a into A' we get A back, up to strict equality. -}
  recoverASet : (a : A) → (A' (m a) ≡ˢ A)
  recoverASet a = congˢ Σ.fst (comm' a)

  {- The "inverse" itself, which in fact belongs to A' b, rather than A, in general. -}
  inverse : (b : B) → (A' b)
  inverse b = Σ.snd (f' b)

  {- If we feed in m a to inverse, we get back a, up to strict equality. -}
  recoverAPoint : (a : A) → (transportˢ (recoverASet a) (inverse (m a)) ≡ˢ a)
  recoverAPoint a = congDˢ Σ.snd (comm' a)
