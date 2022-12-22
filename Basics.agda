{- Some basic type theory propositions that suffice here. -}
module Basics where

open import Agda.Primitive

private variable
  ℓ ℓ' ℓ'' : Level

{- Definition of Σ type. -}
record Σ (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

{- Definition of equality. -}
data _≡_ {A : Set ℓ} : A → A → Set ℓ where
  refl : {a : A} → a ≡ a

{- Transitivity and symmetry of equality. -}
_∙_ : {A : Set ℓ} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
refl ∙ q = q

sym : {A : Set ℓ} {a b : A} → (a ≡ b) → (b ≡ a)
sym refl = refl

{- Definition of isContr -}
isContr : Set ℓ → Set ℓ
isContr A = Σ A (λ x → (y : A) → x ≡ y)

isContrSingl : {A : Set ℓ} (a : A) → isContr (Σ A (λ a' → a ≡ a'))
isContrSingl {A = A} a = (a , refl) , (λ {(a' , p) → path a' p})
  where
    path : (a' : A) → (p : a ≡ a') → (a , refl) ≡ (a' , p) 
    path a' refl = refl

{- Definition of pointed types. -}
Set• : Set₁
Set• = Σ Set (λ x → x)
