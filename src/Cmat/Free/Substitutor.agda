{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinData
open import Cubical.Categories.Limits.Terminal

open import Mat.Signature
open import Mat.Free.Presentation
open import Cmat.Signature
import Mat.Free.Term
open import Mat.Presentation

module Cmat.Free.Substitutor
  (cmatsig : CmatSignature)
  {{_ : CmatSignature.CanBeClosed cmatsig}} where

open CmatSignature cmatsig
open MatSignature matsigClosed

private
  variable m n p q : Mode

data OperationSubstitutor : Jud m⊤ → Type where
  idsub : ∀ {Γ : Ctx m} → OperationSubstitutor (Γ ⊩ sub Γ)
  tmsub : ∀ {Γ Δ : Ctx m} {rhs : RHS m} → OperationSubstitutor (Γ ⊩ rhs)
  -- the following take a delayed substitution:
  applyJHom : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {Φ Ψ : Junctor m n} → OperationSubstitutor (Γ ⊩ sub (Δ ⦊ Ψ))
  applyJunctor : ∀ {m n} {Γ : Ctx n} {Δ Θ : Ctx m} {Φ : Junctor m n} → OperationSubstitutor (Γ ⊩ sub (Θ ⦊ Φ))

isSetOperationSubstitutor : ∀ {J} → isSet (OperationSubstitutor J)
isSetOperationSubstitutor = {!!}

aritySubstitutor : ∀ {J} → OperationSubstitutor J → Arity
aritySubstitutor idsub = []
aritySubstitutor (tmsub {m} {Γ} {Δ} {rhs}) = (Δ ⊩ rhs) ∷ (Γ ⊩ sub Δ) ∷ []
aritySubstitutor (applyJHom {m} {n} {Γ} {Δ} {Φ} {Ψ}) = (Δ ⊩ jhom Φ Ψ) ∷ (Γ ⊩ sub (Δ ⦊ Φ)) ∷ []
aritySubstitutor (applyJunctor {m} {n} {Γ} {Δ} {Θ} {Φ}) = (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub (Δ ⦊ Φ)) ∷ []

fmatSubstitutor : FreeMat matsigClosed
FreeMat.Operation fmatSubstitutor = OperationSubstitutor
FreeMat.isSetOperation fmatSubstitutor = isSetOperationSubstitutor
FreeMat.arity fmatSubstitutor = aritySubstitutor

open Mat.Free.Term fmatSubstitutor

open MatEqTheory

pattern _[_]1 t σ = tmsub $1 (t ∷ σ ∷ [])
infixl 7 _[_]1

{-
data AxiomSubstitutor : Jud → Type where
  tmsub-lUnit : ∀ {Γ Δ : Ctx m} → AxiomSubstitutor (Γ ⊩ sub Δ)
  tmsub-rUnit : ∀ {Γ : Ctx m} {rhs : RHS m} → AxiomSubstitutor (Γ ⊩ rhs)
  tmsub-assoc : ∀ {Γ Δ Θ : Ctx m} {rhs : RHS m} → AxiomSubstitutor (Γ ⊩ rhs)
  idjhom[] : ∀ {Γ' Γ : Ctx m} {Φ : Junctor m n} → AxiomSubstitutor (Γ' ⊩ jhom Φ Φ)
  compjhom[] : ∀ {Γ' Γ : Ctx m} {Φ Ψ Ξ : Junctor m n} → AxiomSubstitutor (Γ' ⊩ jhom Φ Ξ)
  whiskerL[] : ∀ {Γ' Γ : Ctx m} (Ξ : Junctor m n) {Φ Ψ : Junctor n p} → AxiomSubstitutor (Γ' ⊩ jhom (Ξ ⦊' Φ) (Ξ ⦊' Ψ))
  whiskerR[] : ∀ {Γ' Γ : Ctx m} {Φ Ψ : Junctor m n} (Ξ : Junctor n p) → AxiomSubstitutor (Γ' ⊩ jhom (Φ ⦊' Ξ) (Ψ ⦊' Ξ))
  -- the following take a delayed substitution:
  applyJHom[] : ∀ {m n} {Γ' Γ : Ctx n} {Δ : Ctx m} {Φ Ψ : Junctor m n} → AxiomSubstitutor (Γ' ⊩ sub (Δ ⦊ Ψ))
  applyJunctor[] : ∀ {m n} {Γ' Γ : Ctx n} {Δ Θ : Ctx m} {Φ : Junctor m n} → AxiomSubstitutor (Γ' ⊩ sub (Θ ⦊ Φ))
  {-
  - The latter 4 respect identity and composition
  - whiskerL and whiskerR commute
  - applyJHom and applyJunctor commute
  -}

isSetAxiomSubstitutor : ∀ {J} → isSet (AxiomSubstitutor J)
isSetAxiomSubstitutor = {!!}

arityAxiomSubstitutor : ∀ {J} → AxiomSubstitutor J → Arity
arityAxiomSubstitutor (tmsub-lUnit {m} {Γ} {Δ}) = (Γ ⊩ sub Δ) ∷ []
arityAxiomSubstitutor (tmsub-rUnit {m} {Γ} {rhs}) = (Γ ⊩ rhs) ∷ []
arityAxiomSubstitutor (tmsub-assoc {m} {Γ} {Δ} {Θ} {rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
arityAxiomSubstitutor (idjhom[] {m} {n} {Γ'} {Γ} {Φ}) = (Γ' ⊩ sub Γ) ∷ []
arityAxiomSubstitutor (compjhom[] {m} {n} {Γ'} {Γ} {Φ} {Ψ} {Ξ}) = (Γ ⊩ jhom Ψ Ξ) ∷ (Γ ⊩ jhom Φ Ψ) ∷ (Γ' ⊩ sub Γ) ∷ []
arityAxiomSubstitutor (whiskerL[] {m} {n} {p} {Γ'} {Γ} Ξ {Φ} {Ψ}) = (Γ ⦊ Ξ ⊩ jhom Φ Ψ) ∷ (Γ' ⊩ sub Γ) ∷ []
arityAxiomSubstitutor (whiskerR[] {m} {n} {p} {Γ'} {Γ} {Φ} {Ψ} Ξ) = (Γ ⊩ jhom Φ Ψ) ∷ (Γ' ⊩ sub Γ) ∷ []
arityAxiomSubstitutor (applyJHom[] {m} {n} {Γ'} {Γ} {Δ} {Φ} {Ψ}) = (Δ ⊩ jhom Φ Ψ) ∷ (Γ ⊩ sub (Δ ⦊ Φ)) ∷ (Γ' ⊩ sub Γ) ∷ []
arityAxiomSubstitutor (applyJunctor[] {m} {n} {Γ'} {Γ} {Δ} {Θ} {Φ}) = (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub (Δ ⦊ Φ)) ∷ (Γ' ⊩ sub Γ) ∷ []

lhsSubstitutor rhsSubstitutor : ∀ {J} → (axiom : AxiomSubstitutor J)
  → TermF (mtyp (arity2mset (arityAxiomSubstitutor axiom))) J
lhsSubstitutor (tmsub-lUnit {m} {Γ} {Δ}) = (idsub $1 []) [ arvarF zero ]1
lhsSubstitutor (tmsub-rUnit {m} {Γ} {rhs}) = arvarF zero [ idsub $1 [] ]1
lhsSubstitutor tmsub-assoc = arvarF zero [ arvarF one ]1 [ arvarF two ]1
lhsSubstitutor (idjhom[] {m} {n} {Γ'} {Γ} {Φ}) = (idjhom $1 []) [ arvarF zero ]1
lhsSubstitutor (compjhom[] {m} {n} {Γ'} {Γ} {Φ} {Ψ} {Ξ}) =
  (compjhom $1 arvarF zero ∷ arvarF one ∷ []) [ arvarF two ]1
lhsSubstitutor (whiskerL[] {m} {n} {p} {Γ'} {Γ} Ξ {Φ} {Ψ}) =
  (whiskerL Ξ $1 arvarF zero ∷ []) [ arvarF one ]1
lhsSubstitutor (whiskerR[] {m} {n} {p} {Γ'} {Γ} {Φ} {Ψ} Ξ) =
  (whiskerR Ξ $1 arvarF zero ∷ []) [ arvarF one ]1
lhsSubstitutor (applyJHom[] {m} {n} {Γ'} {Γ} {Δ} {Φ} {Ψ}) =
  (applyJHom $1 arvarF zero ∷ arvarF one ∷ []) [ arvarF two ]1
lhsSubstitutor (applyJunctor[] {m} {n} {Γ'} {Γ} {Δ} {Θ} {Φ}) =
  (applyJunctor $1 arvarF zero ∷ arvarF one ∷ []) [ arvarF two ]1
rhsSubstitutor (tmsub-lUnit {m} {Γ} {Δ}) = arvarF zero
rhsSubstitutor (tmsub-rUnit {m} {Γ} {rhs}) = arvarF zero
rhsSubstitutor tmsub-assoc = arvarF zero [ arvarF one [ arvarF two ]1 ]1
rhsSubstitutor (idjhom[] {m} {n} {Γ'} {Γ} {Φ}) = idjhom $1 []
rhsSubstitutor (compjhom[] {m} {n} {Γ'} {Γ} {Φ} {Ψ} {Ξ}) =
  compjhom $1 arvarF zero [ arvarF two ]1 ∷ arvarF one [ arvarF two ]1 ∷ []
rhsSubstitutor (whiskerL[] {m} {n} {p} {Γ'} {Γ} Ξ {Φ} {Ψ}) =
  whiskerL Ξ $1 arvarF zero [ applyJunctor $1 arvarF one ∷ (idsub $1 []) ∷ [] ]1 ∷ []
rhsSubstitutor (whiskerR[] {m} {n} {p} {Γ'} {Γ} {Φ} {Ψ} Ξ) =
  whiskerR Ξ $1 arvarF zero [ arvarF one ]1 ∷ []
rhsSubstitutor (applyJHom[] {m} {n} {Γ'} {Γ} {Δ} {Φ} {Ψ}) =
  applyJHom $1 arvarF zero ∷ arvarF one [ arvarF two ]1 ∷ []
rhsSubstitutor (applyJunctor[] {m} {n} {Γ'} {Γ} {Δ} {Θ} {Φ}) =
  applyJunctor $1 arvarF zero ∷ arvarF one [ arvarF two ]1 ∷ []

eqTheorySubstitutor : MatEqTheory fmatSubstitutor
Axiom eqTheorySubstitutor = AxiomSubstitutor
isSetAxiom eqTheorySubstitutor = isSetAxiomSubstitutor
msetArity eqTheorySubstitutor = arity2mset ∘ arityAxiomSubstitutor
lhs eqTheorySubstitutor = lhsSubstitutor
rhs eqTheorySubstitutor = rhsSubstitutor

open Mat

matSubstitutor : Mat matsigPlant
getFreeMat matSubstitutor = fmatSubstitutor
getMatEqTheory matSubstitutor = eqTheorySubstitutor
-}
