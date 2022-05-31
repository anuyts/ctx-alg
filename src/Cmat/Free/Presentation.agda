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
    CustomOperation : ∀ {m} → RHS m → Type
    isSetCustomOperation : ∀ {m} {rhs : RHS m} → isSet (CustomOperation rhs)
    arityCustom : ∀ {m} {rhs : RHS m} → CustomOperation rhs → CArity m

  private
    variable m n p q : Mode

  data Operation : RHS m → Type where
    custom : ∀ {m} {rhs : RHS m} → CustomOperation rhs → Operation rhs
    id-jhom : ∀ {m n} {Φ : Junctor m n} → Operation (jhom Φ Φ)
    comp-jhom : ∀ {m n} {Φ Ψ Ξ : Junctor m n} → Operation (jhom Φ Ξ)
    whiskerL : ∀ {m n p} (Ξ : Junctor m n) {Φ Ψ : Junctor n p} → Operation (jhom (Ξ ⦊ Φ) (Ξ ⦊ Ψ))
    whiskerR : ∀ {m n p} {Φ Ψ : Junctor m n} (Ξ : Junctor n p) → Operation (jhom (Φ ⦊ Ξ) (Ψ ⦊ Ξ))
    -- whiskerL t ∘ whiskerR s = whiskerR s ∘ whiskerL (t [ Γ.s ])
    -- whiskerL (whiskerR t) = whiskerR (whiskerL t)
    -- whiskerL respects id-jhom and comp-jhom
    -- whiskerR respects id-jhom and comp-jhom
    -- whiskerL respects ◇ and ⦊
    -- whiskerR respects ◇ and ⦊

  isSetOperation : ∀ {m} {rhs : RHS m} → isSet (Operation rhs)
  isSetOperation = {!!} -- via reflection

  arity : ∀ {m} {rhs : RHS m} → Operation rhs → CArity m
  arity (custom o) = arityCustom o
  arity id-jhom = []
  arity (comp-jhom {m} {n} {Φ} {Ψ} {Ξ}) = (◇ ⊩ jhom Φ Ψ) ∷ (◇ ⊩ jhom Ψ Ξ) ∷ []
  arity (whiskerL {m} {n} {p} Ξ {Φ} {Ψ}) = (Ξ ⊩ jhom Φ Ψ) ∷ []
  arity (whiskerR {m} {n} {p} {Φ} {Ψ} Ξ) = (◇ ⊩ jhom Φ Ψ) ∷ []

  -- The cold translation
  module _ (m0 : Mode) where

    fmatCold : FreeMat (matsigOpen m0)
    FreeMat.Operation fmatCold (Γ ⊩ rhs) = Operation rhs
    FreeMat.isSetOperation fmatCold = isSetOperation
    FreeMat.arity fmatCold {Γ ⊩ rhs} o = arityOpen Γ (arity o)

    --open MatEqTheory

    --data AxiomCold : Jud m0 → Type where
