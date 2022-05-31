{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinData
open import Cubical.Categories.Category

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term
open import Mat.Presentation
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

  -- The hot translation
  module _ (m0 : Mode) where

    open MatSignature (matsigOpen m0)

    data OperationHot : Jud m0 → Type where
      inctx : ∀ {m} {Φ : Junctor m0 m} {rhs : RHS m} → (o : Operation rhs) → OperationHot (Φ ⊩ rhs)
      tmsub : ∀ {m} {Φ Ψ : Junctor m0 m} {rhs : RHS m} → OperationHot (Φ ⊩ rhs)

    isSetOperationHot : ∀ {J : Jud m0} → isSet (OperationHot J)
    isSetOperationHot = {!!}

    arityHot : ∀ {J : Jud m0} → OperationHot J → MatSignature.Arity (matsigOpen m0)
    arityHot {Γ ⊩ rhs} (inctx o) = arityOpen Γ (arity o)
    arityHot (tmsub {m} {Γ} {Δ} {rhs}) = (Δ ⊩ rhs) ∷ (◇ ⊩ jhom Γ Δ) ∷ []

    fmatHot : FreeMat (matsigOpen m0)
    FreeMat.Operation fmatHot = OperationHot
    FreeMat.isSetOperation fmatHot = isSetOperationHot
    FreeMat.arity fmatHot = arityHot

    open MatEqTheory
    open Mat.Free.Term fmatHot

    pattern _[_]1 t σ = tmsub $1 (t ∷ σ ∷ [])
    infixl 7 _[_]1

    data AxiomHot : Jud m0 → Type where
      tmsub-rUnit : ∀ {Γ : Junctor m0 m} {rhs : RHS m} → AxiomHot (Γ ⊩ rhs)
      tmsub-assoc : ∀ {Γ Δ Θ : Junctor m0 m} {rhs : RHS m} → AxiomHot (Γ ⊩ rhs)
      tmsub-commut : ∀ {m} {Γ Δ : Junctor m0 m} {rhs : RHS m} (o : Operation rhs) → AxiomHot (Γ ⊩ rhs)

    isSetAxiomHot : ∀ {J} → isSet (AxiomHot J)
    isSetAxiomHot = {!!}

    arityAxiomHot : ∀ {J} → AxiomHot J → Arity
    arityAxiomHot (tmsub-rUnit {m} {Γ} {rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomHot (tmsub-assoc {m} {Γ} {Δ} {Θ} {rhs}) = (Θ ⊩ rhs) ∷ (◇ ⊩ jhom Δ Θ) ∷ (◇ ⊩ jhom Γ Δ) ∷ []
    arityAxiomHot (tmsub-commut {m} {Γ} {Δ} {rhs} o) = (◇ ⊩ jhom Γ Δ) ∷ arityOpen Δ (arity o)

    open Category catModeJunctor renaming (_∘_ to _⊚_)

    lhsHot rhsHot : ∀ {J} → (axiom : AxiomHot J) → TermF (mtyp (arity2mset (arityAxiomHot axiom))) J
    lhsHot tmsub-rUnit = arvarF zero [ inctx id-jhom $1 [] ]1
    lhsHot tmsub-assoc = arvarF zero [ arvarF one ]1 [ arvarF two ]1
    lhsHot (tmsub-commut o) = (inctx o $1 tabulateOverLookup (arityHot (inctx o)) (arvarF ∘ suc)) [ arvarF zero ]1
    rhsHot tmsub-rUnit = arvarF zero
    rhsHot tmsub-assoc = arvarF zero [ inctx comp-jhom $1
      subst (TermF _) (cong (_⊩ _) (sym (⋆IdR ◇))) (arvarF two) ∷
      subst (TermF _) (cong (_⊩ _) (sym (⋆IdR ◇))) (arvarF one)
      ∷ [] ]1
    rhsHot (tmsub-commut o) = inctx o $1 tabulateOverLookup (arityHot (inctx o)) (λ p → (
        {!arvarF (suc p)!} [ {!zero!} ]1
      ))

    eqTheoryHot : MatEqTheory fmatHot
    Axiom eqTheoryHot = AxiomHot
    isSetAxiom eqTheoryHot = isSetAxiomHot
    msetArity eqTheoryHot = arity2mset ∘ arityAxiomHot
    lhs eqTheoryHot = {!!}
    rhs eqTheoryHot = {!!}
