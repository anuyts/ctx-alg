{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List
open import Cubical.Data.FinData

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term
open import Mat.Presentation

module Mat.Instances.MonoidAction where
open FreeMat

data SortMonoidAction : Type where
  theMonoid theSpace : SortMonoidAction

module _ where

  open Signature

  signMonoidAction : Signature
  Sort signMonoidAction = SortMonoidAction
  isSetSort signMonoidAction = {!!}

open Signature signMonoidAction

data OperatorMonoidAction : SortMonoidAction → Type where
  mempty : OperatorMonoidAction theMonoid
  mappend : OperatorMonoidAction theMonoid
  mact : OperatorMonoidAction theSpace

arityMonoidAction : ∀ {sort} → OperatorMonoidAction sort → Arity
arityMonoidAction mempty = []
arityMonoidAction mappend = theMonoid ∷ theMonoid ∷ []
arityMonoidAction mact = theMonoid ∷ theSpace ∷ []

fmatMonoidAction : FreeMat signMonoidAction
Operation fmatMonoidAction = OperatorMonoidAction
isSetOperation fmatMonoidAction = {!!}
arity fmatMonoidAction = arityMonoidAction

open Mat.Free.Term fmatMonoidAction

data AxiomMonoidAction : SortMonoidAction → Type where
  mappend-lUnit : AxiomMonoidAction theMonoid
  mappend-rUnit : AxiomMonoidAction theMonoid
  mappend-Assoc : AxiomMonoidAction theMonoid
  mact-lUnit : AxiomMonoidAction theSpace
  mact-Assoc : AxiomMonoidAction theSpace

arityAxiomMonoidAction : ∀ {sort} → AxiomMonoidAction sort → Arity
arityAxiomMonoidAction mappend-lUnit = theMonoid ∷ []
arityAxiomMonoidAction mappend-rUnit = theMonoid ∷ []
arityAxiomMonoidAction mappend-Assoc = theMonoid ∷ theMonoid ∷ theMonoid ∷ []
arityAxiomMonoidAction mact-lUnit = theSpace ∷ []
arityAxiomMonoidAction mact-Assoc = theMonoid ∷ theMonoid ∷ theSpace ∷ []

lhsMonoidAction rhsMonoidAction : ∀ {sort} → (axiom : AxiomMonoidAction sort) →
  TermF (mtyp (arity2mset (arityAxiomMonoidAction axiom))) sort
lhsMonoidAction mappend-lUnit = mappend $1 λ { zero → mempty $1 λ () ; one → varF (zero , refl)}
lhsMonoidAction mappend-rUnit = mappend $1 λ { zero → varF (zero , refl) ; one → mempty $1 λ ()}
lhsMonoidAction mappend-Assoc = mappend $1 λ where
  zero → mappend $1 λ where
    zero → varF (zero , refl)
    one → varF (one , refl)
  one → varF (two , refl)
lhsMonoidAction mact-lUnit = mact $1 λ { zero → mempty $1 λ () ; one → varF (zero , refl)}
lhsMonoidAction mact-Assoc = mact $1 λ where
  zero → mappend $1 λ where
    zero → varF (zero , refl)
    one → varF (one , refl)
  one → varF (two , refl)
rhsMonoidAction mappend-lUnit = varF (zero , refl)
rhsMonoidAction mappend-rUnit = varF (zero , refl)
rhsMonoidAction mappend-Assoc = mappend $1 λ where
  zero → varF (zero , refl)
  one → mappend $1 λ where
    zero → varF (one , refl)
    one → varF (two , refl)
rhsMonoidAction mact-lUnit = varF (zero , refl)
rhsMonoidAction mact-Assoc = mact $1 λ where
  zero → varF (zero , refl)
  one → mact $1 λ where
    zero → varF (one , refl)
    one → varF (two , refl)

module _ where

  open EqTheory

  eqTheoryMonoidAction : EqTheory fmatMonoidAction
  Axiom eqTheoryMonoidAction = AxiomMonoidAction
  isSetAxiom eqTheoryMonoidAction = {!!}
  msetArity eqTheoryMonoidAction = arity2mset ∘ arityAxiomMonoidAction
  lhs eqTheoryMonoidAction = lhsMonoidAction
  rhs eqTheoryMonoidAction = rhsMonoidAction

module _ where

  open Mat

  matMonoidAction : Mat signMonoidAction
  getFreeMat matMonoidAction = fmatMonoidAction
  getEqTheory matMonoidAction = eqTheoryMonoidAction

open Mat matMonoidAction
