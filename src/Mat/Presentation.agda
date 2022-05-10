{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monad.Base

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term

module Mat.Presentation where

record EqTheory {sign : Signature} (presF : PresentationF sign) : Type where
  open Signature sign
  open PresentationF presF
  open Mat.Free.Term presF
  open Category hiding (_∘_)
  open Functor
  open IsMonad
  open NatTrans

  field
    Axiom : Sort → Type
    isSetAxiom : {sortOut : Sort} → isSet (Axiom sortOut)
    msetArity : ∀ {sortOut} → Axiom sortOut → MSet
    lhs rhs : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → TermF (mtyp (msetArity axiom)) sortOut

record Presentation (sign : Signature) : Type where
  constructor presentation
  field
    getPresentationF : PresentationF sign
    getEqTheory : EqTheory getPresentationF
