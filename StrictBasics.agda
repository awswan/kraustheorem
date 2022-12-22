{- This file contains some basic propositions for working with two level type theory
   including the definition of strict equality. -}
module StrictBasics where

open import Agda.Primitive

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

{- Two elements of a (fibrant) type can be propositionally equal, or satisfy the
   stronger condition of being strictly equal. In the semantics we can ensure
   that definitional equality is interpreted as strict equality. It is possible
   to define strict equality for any two elements of a strict type, but it is
   not needed for these results. -}
data _≡ˢ_ {A : Set ℓ} : A → A → SSet ℓ where
  reflˢ : {a : A} → a ≡ˢ a

{- A strict version of Σ type. We again only define the special case that will
   be needed here. This has an element of a fibrant type as first component
   and a strict type as second component. If B is furthermore a proposition, we
   can think of this a carving out a strict subtype of a fibrant type. -}
record Σˢ (A : Set ℓ) (B : A → SSet ℓ') : SSet (ℓ ⊔ ℓ') where
  field
    fst : A
    snd : (B fst)

{- Version of cong, transport and subst for strict equality. -}
congˢ : {A : Set ℓ} {B : Set ℓ'} (f : A → B) {a a' : A} →
  (a ≡ˢ a') → (f a ≡ˢ f a')
congˢ f reflˢ = reflˢ

transportˢ : {A B : Set ℓ} (p : A ≡ˢ B) → A → B
transportˢ reflˢ a = a

substˢ : {A : Set ℓ} (B : A → Set ℓ') {a a' : A} (p : a ≡ˢ a') → B a → B a'
substˢ B p = transportˢ (congˢ B p)

{- Dependent cong -}
congDˢ : {A : Set ℓ} {B : A → Set ℓ'} (f : (a : A) → B a) →
  {a a' : A} → (p : a ≡ˢ a') → substˢ B p (f a) ≡ˢ f a'
congDˢ f reflˢ = reflˢ
