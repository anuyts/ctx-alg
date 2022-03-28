{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Prod
open import Cubical.Data.W.Indexed
open import Cubical.Data.FinData
open import Cubical.Data.Sum
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty
open import Cubical.Data.Nat
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
    Operation : Sort → Type
    arity : ∀ {sortOut} → Operation sortOut → Arity
    isSetOperation : {sortOut : Sort} → isSet (Operation sortOut)

  record Term1 (precarrier : Precarrier) (sortOut : Sort) : Type where
    inductive
    eta-equality
    constructor term1
    field
      operation : Operation sortOut
      arguments : Arguments precarrier (arity operation)
  open Term1

  RepTerm1 : (precarrier : Precarrier) (sortOut : Sort) → Type
  RepTerm1 precarrier sortOut =
    Σ[ o ∈ Operation sortOut ] Arguments precarrier (arity o)

  isoRepTerm1 : (precarrier : Precarrier) (sortOut : Sort)
    → Term1 precarrier sortOut ≅ RepTerm1 precarrier sortOut
  fun (isoRepTerm1 precarrier sortOut) (term1 o args) = o , args
  inv (isoRepTerm1 precarrier sortOut) (o , args) = term1 o args
  rightInv (isoRepTerm1 precarrier sortOut) (o , args) = refl
  leftInv (isoRepTerm1 precarrier sortOut) (term1 o args) = refl

  pathRepTerm1 : (precarrier : Precarrier) (sortOut : Sort)
    → Term1 precarrier sortOut ≡ RepTerm1 precarrier sortOut
  pathRepTerm1 precarrier sortOut = ua (isoToEquiv (isoRepTerm1 precarrier sortOut))

  isSetRepTerm1 : (precarrier : Precarrier) (sortOut : Sort) → isSet (RepTerm1 precarrier sortOut)
  isSetRepTerm1 precarrier sortOut =
    isOfHLevelΣ 2 isSetOperation (λ o → isSetArguments precarrier (arity o))

  isSetTerm1 : ∀ {precarrier sortOut} → isSet (Term1 precarrier sortOut)
  isSetTerm1 {precarrier} {sortOut} =
    subst⁻ isSet (pathRepTerm1 precarrier sortOut) (isSetRepTerm1 precarrier sortOut)

  precarrierTerm1 : Precarrier → Precarrier
  fst (precarrierTerm1 precarrier sortOut) = Term1 precarrier sortOut
  snd (precarrierTerm1 precarrier sortOut) = isSetTerm1

  ftrTerm1 : Functor catPrecarrier catPrecarrier
  F-ob ftrTerm1 = precarrierTerm1
  F-hom ftrTerm1 {x = precX} {y = precY} φ sortOut (term1 o args) =
    term1 o λ p → φ (arity o ! p) (args p)
  F-id ftrTerm1 {x = precX} = refl
  F-seq ftrTerm1 {x = precX} {y = precY} {z = precZ} φ χ = refl

  module _ where

    data TermF (metavar : Precarrier) : (sortOut : Sort) → Type
    isSetTermF : (metavar : Precarrier) (sortOut : Sort) → isSet (TermF metavar sortOut)
  
    precarrierTermF : Precarrier → Precarrier
    fst (precarrierTermF metavar sortOut) = TermF metavar sortOut
    snd (precarrierTermF metavar sortOut) = isSetTermF metavar sortOut
  
    data TermF metavar where
      varF : ∀ {sortOut} → typ (metavar sortOut) → TermF metavar sortOut
      astF : ∀ {sortOut} → Term1 (precarrierTermF metavar) sortOut → TermF metavar sortOut

    RepTermF : (metavar : Precarrier) (sortOut : Sort) → Type
    RepTermF metavar sortOut =
      IW (λ sort → typ (metavar sort) ⊎ Operation sort)
        (λ sort → ⊎.elim (λ v → ⊥) λ o → Fin (length (arity o)))
        (λ sort → ⊎.elim (λ v ()) (λ o p → arity o ! p))
        sortOut

    toRepTermF : (metavar : Precarrier) (sortOut : Sort) → TermF metavar sortOut → RepTermF metavar sortOut
    toRepTermF metavar sortOut (varF v) = node (inl v) (λ ())
    toRepTermF metavar sortOut (astF (term1 o args)) =
      node (inr o) λ p → toRepTermF metavar (arity o ! p) (args p)

    fromRepTermF : (metavar : Precarrier) (sortOut : Sort) → RepTermF metavar sortOut → TermF metavar sortOut
    fromRepTermF metavar sortOut (node (inl v) u) = varF v
    fromRepTermF metavar sortOut (node (inr o) args) = astF (term1 o λ p → fromRepTermF metavar (arity o ! p) (args p))
  
    fromToRepTermF : (metavar : Precarrier) (sortOut : Sort) (t : TermF metavar sortOut)
      → fromRepTermF metavar sortOut (toRepTermF metavar sortOut t) ≡ t
    fromToRepTermF metavar sortOut (varF v) = refl
    fromToRepTermF metavar sortOut (astF (term1 o args)) i =
      astF (term1 o λ p → fromToRepTermF metavar (arity o ! p) (args p) i)

    toFromRepTermF : (metavar : Precarrier) (sortOut : Sort) (rt : RepTermF metavar sortOut)
      → toRepTermF metavar sortOut (fromRepTermF metavar sortOut rt) ≡ rt
    toFromRepTermF metavar sortOut (node (inl v) u) = cong (node (inl v)) (funExt (λ ()))
    toFromRepTermF metavar sortOut (node (inr o) args) i =
      node (inr o) (λ p → toFromRepTermF metavar (arity o ! p) (args p) i)

    isoRepTermF : (metavar : Precarrier) (sortOut : Sort) → TermF metavar sortOut ≅ RepTermF metavar sortOut
    fun (isoRepTermF metavar sortOut) = toRepTermF metavar sortOut
    inv (isoRepTermF metavar sortOut) = fromRepTermF metavar sortOut
    rightInv (isoRepTermF metavar sortOut) = toFromRepTermF metavar sortOut
    leftInv (isoRepTermF metavar sortOut) = fromToRepTermF metavar sortOut

    pathRepTermF : (metavar : Precarrier) (sortOut : Sort) → TermF metavar sortOut ≡ RepTermF metavar sortOut
    pathRepTermF metavar sortOut = ua (isoToEquiv (isoRepTermF metavar sortOut))
  
    isSetRepTermF : (metavar : Precarrier) (sortOut : Sort) → isSet (RepTermF metavar sortOut)
    isSetRepTermF metavar sortOut = isOfHLevelSuc-IW 1 (λ sort → isSet⊎ (str (metavar sort)) isSetOperation) sortOut
  
    isSetTermF metavar sortOut = subst⁻ isSet (pathRepTermF metavar sortOut) (isSetRepTermF metavar sortOut)

open Presentation {{...}} public
