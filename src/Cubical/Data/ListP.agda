{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat

module Cubical.Data.ListP where

open _≅_

data ListP {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) : (as : List A) → Type (ℓ-max ℓA ℓB) where
  [] : ListP B []
  _∷_ : {x : A} (y : B x) {xs : List A} (ys : ListP B xs) → ListP B (x ∷ xs)

RepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → Type (ℓ-max ℓA ℓB)
RepListP B [] = Lift Unit
RepListP B (a ∷ as) = B a × RepListP B as

isoRepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → ListP B as ≅ RepListP B as
fun (isoRepListP B []) bs = lift tt
inv (isoRepListP B []) u = []
rightInv (isoRepListP B []) u = refl
leftInv (isoRepListP B []) [] = refl
fun (isoRepListP B (a ∷ as)) (b ∷ bs) = b , fun (isoRepListP B as) bs
inv (isoRepListP B (a ∷ as)) (b , br) = b ∷ inv (isoRepListP B as) br
rightInv (isoRepListP B (a ∷ as)) (b , br) i = b , rightInv (isoRepListP B as) br i
leftInv (isoRepListP B (a ∷ as)) (b ∷ bs) i = b ∷ leftInv (isoRepListP B as) bs i

equivRepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → ListP B as ≃ RepListP B as
equivRepListP B as = isoToEquiv (isoRepListP B as)

pathRepListP : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) (as : List A) → ListP B as ≡ RepListP B as
pathRepListP B as = ua (equivRepListP B as)

isOfHLevelRepListP : ∀ {ℓA ℓB} (n : HLevel)
  → {A : Type ℓA}
  → {B : A → Type ℓB} → ((a : A) → isOfHLevel (suc (suc n)) (B a))
  → (as : List A)
  → isOfHLevel (suc (suc n)) (RepListP B as)
isOfHLevelRepListP n isHB [] = isOfHLevelLift (suc (suc n)) (isOfHLevelUnit (suc (suc n)))
isOfHLevelRepListP n isHB (a ∷ as) = isOfHLevelProd (suc (suc n)) (isHB a) (isOfHLevelRepListP n isHB as)

isOfHLevelListP : ∀ {ℓA ℓB} (n : HLevel)
  → {A : Type ℓA}
  → {B : A → Type ℓB} → ((a : A) → isOfHLevel (suc (suc n)) (B a))
  → {as : List A}
  → isOfHLevel (suc (suc n)) (ListP B as)
isOfHLevelListP n {A} {B} isHB {as} =
  transport⁻ (λ i → isOfHLevel (suc (suc n)) (pathRepListP B as i)) (isOfHLevelRepListP n isHB as)

isSetListP : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} → (∀ a → isSet (B a)) → ∀ {as} → isSet (ListP B as)
isSetListP isSetB = isOfHLevelListP 0 isSetB
