{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.List

open import Mat.Signature
open import Mat.Free.Presentation
open import Cmat.Signature

module Cmat.Free.Presentation where

record FreeCmat (cmatsig : CmatSignature) : Type where
  open CmatSignature cmatsig

  field
    Operation : ∀ {m} → RHS m → Type
    isSetOperation : ∀ {m} {rhs : RHS m} → isSet (Operation rhs)
    arity : ∀ {m} {rhs : RHS m} → Operation rhs → CArity m

  -- The cold translation
  module _ where

    fmatCold : (m0 : Mode) → FreeMat (matsigPlant m0)
    FreeMat.Operation (fmatCold m0) (Γ ⊩ rhs) = Operation rhs
    FreeMat.isSetOperation (fmatCold m0) = isSetOperation
    FreeMat.arity (fmatCold m0) {Γ ⊩ rhs} o = plantArity Γ (arity o)
