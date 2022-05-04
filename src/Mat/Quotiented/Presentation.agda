{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term

module Mat.Quotiented.Presentation where

module EqTheory {sign : Signature} (presF : PresentationF sign) where
  open Signature sign
  open PresentationF presF
  open Mat.Free.Term presF
  record EqTheory : Type where

    field
      Axiom : Sort → Type
      isSetAxiom : {sortOut : Sort} → isSet (Axiom sortOut)
      msetArity : ∀ {sortOut} → Axiom sortOut → MSet
      lhs rhs : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → TermF (mtyp (msetArity axiom)) sortOut

  module _ (eqTheory : EqTheory) where
    open EqTheory eqTheory public

    data Term (X : MType) : (sort : Sort) → Type where
      var : ∀ {sortOut} → X sortOut → Term X sortOut
      ast : ∀ {sortOut} → Term1 (Term X) sortOut → Term X sortOut
      astQ : ∀ {sortOut} → TermF (Term X) sortOut → Term X sortOut
      astQ-varF : ∀ {sortOut} → (t : Term X sortOut) → astQ (varF t) ≡ t
      astQ-astF : ∀ {sortOut} → (t : Term1 (TermF (Term X)) sortOut)
        → astQ (astF t) ≡ ast (mapTerm1 (λ sort → astQ) sortOut t)
      byAxiom : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → Term X sort)
        → astQ (mapTermF f sortOut (lhs axiom))
        ≡ astQ (mapTermF f sortOut (rhs axiom))
      isSetTerm : ∀ {sortOut} → isSet (Term X sortOut)

    joinTerm : {X : MType} → (sort : Sort) → Term (Term X) sort → Term X sort
    mapTermF-joinTerm : {X : MType} → (sort : Sort) → TermF (Term (Term X)) sort → TermF (Term X) sort
    mapTerm1-mapTermF-joinTerm : {X : MType} → (sort : Sort) → Term1 (TermF (Term (Term X))) sort → Term1 (TermF (Term X)) sort
    mapTermF-joinTerm-f : {X Y : MType}
      → (f : ∀ sort → Y sort → Term (Term X) sort)
      → (sort : Sort) → (t : TermF Y sort)
      → mapTermF (λ sort' → joinTerm sort' ∘ f sort') sort t ≡ mapTermF-joinTerm sort (mapTermF f sort t)

    joinTerm sort (var t) = t
    joinTerm sort (ast (term1 o args)) = ast (term1 o λ p → joinTerm (arity o ! p) (args p))
    joinTerm sort (astQ t) = astQ (mapTermF-joinTerm sort t)
    joinTerm sort (astQ-varF t i) = astQ-varF (joinTerm sort t) i
    joinTerm sort (astQ-astF t i) = astQ-astF (mapTerm1-mapTermF-joinTerm sort t) i
    joinTerm sort (byAxiom axiom f i) = hcomp
      (λ where
         j (i = i0) → astQ (mapTermF-joinTerm-f f sort (lhs axiom) j)
         j (i = i1) → astQ (mapTermF-joinTerm-f f sort (rhs axiom) j)
      )
      (byAxiom axiom (λ sort' y → joinTerm sort' (f sort' y)) i)
    joinTerm sort (isSetTerm t1 t2 et et' i j) = isSetTerm
      (joinTerm sort t1)
      (joinTerm sort t2)
      (λ k → joinTerm sort (et k))
      (λ k → joinTerm sort (et' k)) i j
    mapTermF-joinTerm sort (varF t) = varF (joinTerm sort t)
    mapTermF-joinTerm sort (astF t) = astF (mapTerm1-mapTermF-joinTerm sort t)
    mapTerm1-mapTermF-joinTerm sort (term1 o args) = term1 o λ p → mapTermF-joinTerm (arity o ! p) (args p)
    mapTermF-joinTerm-f f sort (varF y) i = varF (joinTerm sort (f sort y))
    mapTermF-joinTerm-f f sort (astF (term1 o args)) i =
      astF (term1 o λ p → mapTermF-joinTerm-f f (arity o ! p) (args p) i)

EqTheory = EqTheory.EqTheory

record Presentation (sign : Signature) : Type where
  constructor presentationQ
  field
    getPresentationF : PresentationF sign
    getEqTheory : EqTheory getPresentationF
