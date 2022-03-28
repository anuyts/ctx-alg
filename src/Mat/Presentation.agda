{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.List.Dependent
open import Cubical.Data.Prod
open import Cubical.Data.W.Indexed
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

  record Term1 (precarrier : Precarrier) (sortOut : Sort) : Type where
    inductive
    eta-equality
    constructor term1
    field
      {sortsMid} : Arity
      operation : Operation sortsMid sortOut
      args : ListP (λ sortMid → typ (precarrier sortMid)) sortsMid
  open Term1

  RepTerm1 : (precarrier : Precarrier) (sortOut : Sort) → Type
  RepTerm1 precarrier sortOut =
    Σ[ sortsMid ∈ Arity ] Operation sortsMid sortOut × ListP (λ sortMid → typ (precarrier sortMid)) sortsMid

  isoRepTerm1 : (precarrier : Precarrier) (sortOut : Sort)
    → Term1 precarrier sortOut ≅ RepTerm1 precarrier sortOut
  fun (isoRepTerm1 precarrier sortOut) (term1 o args) = _ , o , args
  inv (isoRepTerm1 precarrier sortOut) (_ , o , args) = term1 o args
  rightInv (isoRepTerm1 precarrier sortOut) (_ , o , args) = refl
  leftInv (isoRepTerm1 precarrier sortOut) (term1 o args) = refl

  pathRepTerm1 : (precarrier : Precarrier) (sortOut : Sort)
    → Term1 precarrier sortOut ≡ RepTerm1 precarrier sortOut
  pathRepTerm1 precarrier sortOut = ua (isoToEquiv (isoRepTerm1 precarrier sortOut))

  isSetRepTerm1 : (precarrier : Precarrier) (sortOut : Sort) → isSet (RepTerm1 precarrier sortOut)
  isSetRepTerm1 precarrier sortOut =
    isOfHLevelΣ 2 isSetArity (λ sortsMid →
      isOfHLevelProd 2 isSetOperation (isOfHLevelSucSuc-ListP 0 (λ sortMid → str (precarrier sortMid)))
    )

  isSetTerm1 : ∀ {precarrier sortOut} → isSet (Term1 precarrier sortOut)
  isSetTerm1 {precarrier} {sortOut} =
    subst⁻ isSet (pathRepTerm1 precarrier sortOut) (isSetRepTerm1 precarrier sortOut)

  precarrierTerm1 : Precarrier → Precarrier
  fst (precarrierTerm1 precarrier sortOut) = Term1 precarrier sortOut
  snd (precarrierTerm1 precarrier sortOut) = isSetTerm1

  ftrTerm1 : Functor catPrecarrier catPrecarrier
  F-ob ftrTerm1 = precarrierTerm1
  F-hom ftrTerm1 {x = precX} {y = precY} φ sortOut (term1 {sortsMid} o args) =
    term1 o (mapOverIdfun φ sortsMid args)
  F-id ftrTerm1 {x = precX} i sortOut (term1 {sortsMid} o args) =
    term1 o (mapOverIdfun-idfun sortsMid i args)
  F-seq ftrTerm1 {x = precX} {y = precY} {z = precZ} φ χ i sortOut (term1 {sortsMid} o args) =
    term1 o (mapOverIdfun-∘ χ φ sortsMid i args)

  data TermF (metavar : Precarrier) : (sortOut : Sort) → Type
  precarrierTermF : Precarrier → Precarrier
  
  data TermF metavar where
    var : ∀ {sortOut} → typ (metavar sortOut) → TermF metavar sortOut
    ast : ∀ {sortOut} → Term1 (precarrierTermF metavar) sortOut → TermF metavar sortOut

  RepTermF : (precarrier : Precarrier) (sortOut : Sort) → Type
  RepTermF precarrier sortOut =
    IW {!!} {!!} {!!} {!!}

  fst (precarrierTermF metavar sortOut) = TermF metavar sortOut
  snd (precarrierTermF metavar sortOut) = {!!}

open Presentation {{...}} public
