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
import Mat.Free.TermQ

module Mat.Presentation where

record EqTheory {sign : Signature} (presF : FreeMat sign) : Type where
  open Signature sign
  open FreeMat presF
  open Mat.Free.TermQ presF
  open Category hiding (_∘_)
  open Functor
  open IsMonad
  open NatTrans

  field
    Axiom : Sort → Type
    isSetAxiom : {sortOut : Sort} → isSet (Axiom sortOut)
    msetArity : ∀ {sortOut} → Axiom sortOut → MSet
    lhs rhs : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → TermF (mtyp (msetArity axiom)) sortOut

record Mat (sign : Signature) : Type where
  constructor mat
  field
    getFreeMat : FreeMat sign
    getEqTheory : EqTheory getFreeMat
