{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.List.Dependent
open import Cubical.Data.Prod
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TypeProduct

open import Mat.Signature

module Mat.Presentation where

open _≅_
open Functor

record Presentation {{sign : Signature}} : Type where
  field
    Operation : Arity → Sort → Type
    isSetOperation : {sortsIn : Arity} → {sortOut : Sort} → isSet (Operation sortsIn sortOut)

  record AppliedOperation (precarrier : Precarrier) (sortOut : Sort) : Type where
    eta-equality
    constructor applyOperation
    field
      {sortsMid} : Arity
      operation : Operation sortsMid sortOut
      args : ListP (λ sortMid → typ (precarrier sortMid)) sortsMid
  open AppliedOperation

  RepAppliedOperation : (precarrier : Precarrier) (sortOut : Sort) → Type
  RepAppliedOperation precarrier sortOut =
    Σ[ sortsMid ∈ Arity ] Operation sortsMid sortOut × ListP (λ sortMid → typ (precarrier sortMid)) sortsMid

  isoRepAppliedOperation : (precarrier : Precarrier) (sortOut : Sort)
    → AppliedOperation precarrier sortOut ≅ RepAppliedOperation precarrier sortOut
  fun (isoRepAppliedOperation precarrier sortOut) (applyOperation o args) = _ , o , args
  inv (isoRepAppliedOperation precarrier sortOut) (_ , o , args) = applyOperation o args
  rightInv (isoRepAppliedOperation precarrier sortOut) (_ , o , args) = refl
  leftInv (isoRepAppliedOperation precarrier sortOut) (applyOperation o args) = refl

  pathRepAppliedOperation : (precarrier : Precarrier) (sortOut : Sort)
    → AppliedOperation precarrier sortOut ≡ RepAppliedOperation precarrier sortOut
  pathRepAppliedOperation precarrier sortOut = ua (isoToEquiv (isoRepAppliedOperation precarrier sortOut))

  isSetRepAppliedOperation : (precarrier : Precarrier) (sortOut : Sort) → isSet (RepAppliedOperation precarrier sortOut)
  isSetRepAppliedOperation precarrier sortOut =
    isOfHLevelΣ 2 isSetArity (λ sortsMid →
      isOfHLevelProd 2 isSetOperation (isOfHLevelSucSuc-ListP 0 (λ sortMid → str (precarrier sortMid)))
    )

  isSetAppliedOperation : ∀ {precarrier sortOut} → isSet (AppliedOperation precarrier sortOut)
  isSetAppliedOperation {precarrier} {sortOut} =
    subst⁻ isSet (pathRepAppliedOperation precarrier sortOut) (isSetRepAppliedOperation precarrier sortOut)

  precarrierAppliedOperation : Precarrier → Precarrier
  fst (precarrierAppliedOperation precarrier sortOut) = AppliedOperation precarrier sortOut
  snd (precarrierAppliedOperation precarrier sortOut) = isSetAppliedOperation

  ftrAppliedOperation : Functor catPrecarrier catPrecarrier
  F-ob ftrAppliedOperation = precarrierAppliedOperation
  F-hom ftrAppliedOperation {x = precX} {y = precY} φ sortOut (applyOperation {sortsMid} o args) =
    applyOperation o (mapOverIdfun φ sortsMid args)
  F-id ftrAppliedOperation {x = precX} i sortOut (applyOperation {sortsMid} o args) =
    applyOperation o (mapOverIdfun-idfun sortsMid i args)
  F-seq ftrAppliedOperation {x = precX} {y = precY} {z = precZ} φ χ i sortOut (applyOperation {sortsMid} o args) =
    applyOperation o (mapOverIdfun-∘ χ φ sortsMid i args)

open Presentation {{...}} public
