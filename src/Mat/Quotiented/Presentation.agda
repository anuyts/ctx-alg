{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Categories.Category

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term

module Mat.Quotiented.Presentation where

record EqTheory {sign : Signature} (presF : PresentationF sign) : Type where
  open Signature sign
  open PresentationF presF
  open Mat.Free.Term presF

  field
    Axiom : Sort → Type
    isSetAxiom : {sortOut : Sort} → isSet (Axiom sortOut)
    msetArity : ∀ {sortOut} → Axiom sortOut → MSet
    lhs rhs : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → TermF (mtyp (msetArity axiom)) sortOut
    
  -- Syntax monad
  data Term (X : MType) : (sortOut : Sort) → Type
  isSetTerm' : (msetX : MSet) (sortOut : Sort) → isSet (Term (mtyp msetX) sortOut)
  termFtoQ : {X : MType} → (sort : Sort) → TermF X sort → Term X sort
  joinTerm : {X : MType} → (sort : Sort) → Term (Term X) sort → Term X sort

  -- Term acting on MSets
  msetTerm : MSet → MSet
  fst (msetTerm msetX sortOut) = Term (mtyp msetX) sortOut
  snd (msetTerm msetX sortOut) = isSetTerm' msetX sortOut

  data Term X where
    var : ∀ {sortOut} → X sortOut → Term X sortOut
    ast : ∀ {sortOut} → Term1 (Term X) sortOut → Term X sortOut
    {-
    astQ : ∀ {sortOut} → TermF (Term X) sortOut → Term X sortOut
    astQ-varF : ∀ {sortOut} → (t : Term X sortOut) → astQ (varF t) ≡ t
    astQ-astF : ∀ {sortOut} → (t : Term1 (TermF (Term X)) sortOut)
      → astQ (astF t) ≡ ast (mapTerm1 (λ sort → astQ) sortOut t)
    -}
    byAxiom : ∀ {sortOut} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → Term X sort)
      → joinTerm sortOut (termFtoQ sortOut (mapTermF f sortOut (lhs axiom)))
       ≡ joinTerm sortOut (termFtoQ sortOut (mapTermF f sortOut (rhs axiom)))
    isSetTerm : ∀ {sortOut} → isSet (Term X sortOut)

  isSetTerm' msetX sortOut = isSetTerm

  termFtoQ sort (varF x) = var x
  termFtoQ sort (astF (term1 o args)) = ast (term1 o λ p → termFtoQ (arity o ! p) (args p))

  joinTerm sort (var t) = t
  joinTerm sort (ast (term1 o args)) = ast (term1 o λ p → joinTerm (arity o ! p) (args p))
  joinTerm sort (byAxiom axiom f i) = {!!}
  joinTerm sort (isSetTerm t t₁ x y i i₁) = {!!}

record Presentation (sign : Signature) : Type where
  constructor presentationQ
  field
    getPresentationF : PresentationF sign
    getEqTheory : EqTheory getPresentationF
