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

    fmatCold : FreeMat matsig
    FreeMat.Operation fmatCold (Γ ⊩ rhs) = Operation rhs
    FreeMat.isSetOperation fmatCold = isSetOperation
    FreeMat.arity fmatCold {Γ ⊩ rhs} o = plantArity Γ (arity o)

-- The open translation
module _ {cmatsig : CmatSignature} (fcmat : FreeCmat cmatsig) (m0 : CmatSignature.Mode cmatsig) where

  module C = CmatSignature cmatsig
  module OC = CmatSignature (cmatsigOpen cmatsig m0)
  module F = FreeCmat fcmat
  open CmatSignature
  open FreeCmat

  OperationOpen : ∀ {m} → OC.RHS m → Type
  OperationOpen (custom (custom crhs)) = Operation fcmat (custom crhs)
  OperationOpen (custom (sub Γ)) = Operation fcmat (sub Γ)
  OperationOpen (sub Γ) = ⊥
  OperationOpen (jhom Ψ Φ) = Operation fcmat (jhom Ψ Φ)

  isSetOperationOpen : ∀ {m} {rhs : OC.RHS m} → isSet (OperationOpen rhs)
  isSetOperationOpen {m} {custom (custom crhs)} = F.isSetOperation
  isSetOperationOpen {m} {custom (sub Γ)} = F.isSetOperation
  isSetOperationOpen {m} {sub Γ} = isProp→isSet isProp⊥
  isSetOperationOpen {m} {jhom Ψ Φ} = F.isSetOperation

  arityOpen : ∀ {m : C.Mode} {rhs : OC.RHS m} → OperationOpen rhs → OC.CArity m
  arityOpen {m} {custom (custom crhs)} o = arityOrig→Open cmatsig (arity fcmat o)
  arityOpen {m} {custom (sub Γ)} o = arityOrig→Open cmatsig (arity fcmat o)
  arityOpen {m} {jhom Ψ Φ} o = arityOrig→Open cmatsig (arity fcmat o)

  fcmatOpen : FreeCmat (cmatsigOpen cmatsig m0)
  Operation fcmatOpen = OperationOpen
  isSetOperation fcmatOpen {m} {rhs} = isSetOperationOpen {m} {rhs}
  arity fcmatOpen {m} {rhs} = arityOpen {m} {rhs}
