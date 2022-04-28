{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Instances.FunctorAlgebras

open import Mat.Signature

module Mat.Free.Presentation where

open _≅_
open Category
open Functor

-- Type of free MAT presentations (MAT presentations without equations)
record PresentationF (sign : Signature) : Type where
  open Signature sign

  field
    Operation : Sort → Type
    isSetOperation : {sortOut : Sort} → isSet (Operation sortOut)
    arity : ∀ {sortOut} → Operation sortOut → Arity
  --  Equation : Type
  --  XEquation : Equation → Type

  --field
  --  lhsRep : (e : Equation) → {!!}

  -- Syntax functor
  record Term1 (X : MType) (sortOut : Sort) : Type where
    inductive
    eta-equality
    constructor term1
    field
      operation : Operation sortOut
      arguments : Arguments X (arity operation)
  open Term1

  RepTerm1 : (X : MType) (sortOut : Sort) → Type
  RepTerm1 X sortOut = Σ[ o ∈ Operation sortOut ] Arguments X (arity o)

  isoRepTerm1 : (X : MType) (sortOut : Sort)
    → Term1 X sortOut ≅ RepTerm1 X sortOut
  fun (isoRepTerm1 X sortOut) (term1 o args) = o , args
  inv (isoRepTerm1 X sortOut) (o , args) = term1 o args
  rightInv (isoRepTerm1 X sortOut) (o , args) = refl
  leftInv (isoRepTerm1 X sortOut) (term1 o args) = refl

  pathRepTerm1 : (X : MType) (sortOut : Sort)
    → Term1 X sortOut ≡ RepTerm1 X sortOut
  pathRepTerm1 X sortOut = ua (isoToEquiv (isoRepTerm1 X sortOut))

  isSetRepTerm1 : (msetX : MSet) (sortOut : Sort) → isSet (RepTerm1 (mtyp msetX) sortOut)
  isSetRepTerm1 msetX sortOut =
    isOfHLevelΣ 2 isSetOperation (λ o → isSetArguments msetX (arity o))

  isSetTerm1 : (msetX : MSet) (sortOut : Sort) →  isSet (Term1 (mtyp msetX) sortOut)
  isSetTerm1 msetX sortOut =
    subst⁻ isSet (pathRepTerm1 (mtyp msetX) sortOut) (isSetRepTerm1 msetX sortOut)

  msetTerm1 : MSet → MSet
  fst (msetTerm1 mset sortOut) = Term1 (mtyp mset) sortOut
  snd (msetTerm1 mset sortOut) = isSetTerm1 mset sortOut

  ftrTerm1 : Functor catMSet catMSet
  F-ob ftrTerm1 = msetTerm1
  F-hom ftrTerm1 {x = msetX} {y = msetY} φ sortOut (term1 o args) =
    term1 o λ p → φ (arity o ! p) (args p)
  F-id ftrTerm1 {x = msetX} = refl
  F-seq ftrTerm1 {x = msetX} {y = msetY} {z = precZ} φ χ = refl

  catModel1 : Category ℓ-zero ℓ-zero
  catModel1 = AlgebrasCategory ftrTerm1

  Model1 : Type ℓ-zero
  Model1 = ob catModel1

  Model1Hom : (m1A m1B : Model1) → Type ℓ-zero
  Model1Hom = Hom[_,_] catModel1

  ftrForgetModel1 : Functor catModel1 catMSet
  ftrForgetModel1 = ForgetAlgebra ftrTerm1
