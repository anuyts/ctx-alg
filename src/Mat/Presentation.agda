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

open import Mat.Signature

module Mat.Presentation where

open _≅_
open Functor

record Presentation {{sign : Signature}} : Type where
  field
    Operation : Arity → Sort → Type
    isSetOperation : {sortsIn : Arity} → {sortOut : Sort} → isSet (Operation sortsIn sortOut)

  record AppliedOperation (hSetSortsIn : Precarrier) (sortOut : Sort) : Type where
    eta-equality
    constructor applyOperation
    field
      {sortsMid} : Arity
      operation : Operation sortsMid sortOut
      args : ListP (λ sortMid → typ (hSetSortsIn sortMid)) sortsMid
  open AppliedOperation

  RepAppliedOperation : (hSetSortsIn : Precarrier) (sortOut : Sort) → Type
  RepAppliedOperation hSetSortsIn sortOut =
    Σ[ sortsMid ∈ Arity ] Operation sortsMid sortOut × ListP (λ sortMid → typ (hSetSortsIn sortMid)) sortsMid

  isoRepAppliedOperation : (hSetSortsIn : Precarrier) (sortOut : Sort)
    → AppliedOperation hSetSortsIn sortOut ≅ RepAppliedOperation hSetSortsIn sortOut
  fun (isoRepAppliedOperation hSetSortsIn sortOut) (applyOperation o args) = _ , o , args
  inv (isoRepAppliedOperation hSetSortsIn sortOut) (_ , o , args) = applyOperation o args
  rightInv (isoRepAppliedOperation hSetSortsIn sortOut) (_ , o , args) = refl
  leftInv (isoRepAppliedOperation hSetSortsIn sortOut) (applyOperation o args) = refl

  pathRepAppliedOperation : (hSetSortsIn : Precarrier) (sortOut : Sort)
    → AppliedOperation hSetSortsIn sortOut ≡ RepAppliedOperation hSetSortsIn sortOut
  pathRepAppliedOperation hSetSortsIn sortOut = ua (isoToEquiv (isoRepAppliedOperation hSetSortsIn sortOut))

  isSetRepAppliedOperation : (hSetSortsIn : Precarrier) (sortOut : Sort) → isSet (RepAppliedOperation hSetSortsIn sortOut)
  isSetRepAppliedOperation hSetSortsIn sortOut =
    isOfHLevelΣ 2 isSetArity (λ sortsMid →
      isOfHLevelProd 2 isSetOperation (isOfHLevelSucSuc-ListP 0 (λ sortMid → str (hSetSortsIn sortMid)))
    )

  isSetAppliedOperation : ∀ {hSetSortsIn sortOut} → isSet (AppliedOperation hSetSortsIn sortOut)
  isSetAppliedOperation {hSetSortsIn} {sortOut} =
    subst⁻ isSet (pathRepAppliedOperation hSetSortsIn sortOut) (isSetRepAppliedOperation hSetSortsIn sortOut)

  ftrAppliedOperation : Functor (SET _) (SET _)
  F-ob ftrAppliedOperation = {!AppliedOperation A , ?!}
  F-hom ftrAppliedOperation = {!!}
  F-id ftrAppliedOperation = {!!}
  F-seq ftrAppliedOperation = {!!}

open Presentation {{...}} public
