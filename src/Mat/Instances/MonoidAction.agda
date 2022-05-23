{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List
open import Cubical.Data.List.Dependent
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

  open MatSignature

  matsigMonoidAction : MatSignature
  Sort matsigMonoidAction = SortMonoidAction
  isGroupoidSort matsigMonoidAction = {!!}

open MatSignature matsigMonoidAction

data OperatorMonoidAction : SortMonoidAction → Type where
  mempty : OperatorMonoidAction theMonoid
  mappend : OperatorMonoidAction theMonoid
  mact : OperatorMonoidAction theSpace

arityMonoidAction : ∀ {sort} → OperatorMonoidAction sort → Arity
arityMonoidAction mempty = []
arityMonoidAction mappend = theMonoid ∷ theMonoid ∷ []
arityMonoidAction mact = theMonoid ∷ theSpace ∷ []

fmatMonoidAction : FreeMat matsigMonoidAction
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
lhsMonoidAction mappend-lUnit = mappend $1 ((mempty $1 []) ∷ arvarF zero ∷ [])
lhsMonoidAction mappend-rUnit = mappend $1 (arvarF zero ∷ (mempty $1 []) ∷ [])
lhsMonoidAction mappend-Assoc = mappend $1 ((mappend $1 (arvarF zero ∷ arvarF one ∷ [])) ∷ arvarF two ∷ [])
lhsMonoidAction mact-lUnit = mact $1 ((mempty $1 []) ∷ arvarF zero ∷ [])
lhsMonoidAction mact-Assoc = mact $1 ((mappend $1 (arvarF zero ∷ arvarF one ∷ [])) ∷ arvarF two ∷ [])
rhsMonoidAction mappend-lUnit = arvarF zero
rhsMonoidAction mappend-rUnit = arvarF zero
rhsMonoidAction mappend-Assoc = mappend $1 (arvarF zero ∷ (mappend $1 (arvarF one ∷ arvarF two ∷ [])) ∷ [])
rhsMonoidAction mact-lUnit = arvarF zero
rhsMonoidAction mact-Assoc = mact $1 (arvarF zero ∷ (mact $1 (arvarF one ∷ arvarF two ∷ [])) ∷ [])

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

  matMonoidAction : Mat matsigMonoidAction
  getFreeMat matMonoidAction = fmatMonoidAction
  getEqTheory matMonoidAction = eqTheoryMonoidAction

open Mat matMonoidAction
