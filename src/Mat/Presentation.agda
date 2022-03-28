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

  module _ where

    data TermF (X : MType) : (sortOut : Sort) → Type
    isSetTermF : (msetX : MSet) (sortOut : Sort) → isSet (TermF (mtyp msetX) sortOut)
  
    msetTermF : MSet → MSet
    fst (msetTermF msetX sortOut) = TermF (mtyp msetX) sortOut
    snd (msetTermF msetX sortOut) = isSetTermF msetX sortOut
  
    data TermF X where
      varF : ∀ {sortOut} → X sortOut → TermF X sortOut
      astF : ∀ {sortOut} → Term1 (TermF X) sortOut → TermF X sortOut

    RepTermF : (X : MType) (sortOut : Sort) → Type
    RepTermF X sortOut =
      IW (λ sort → X sort ⊎ Operation sort)
        (λ sort → ⊎.elim (λ v → ⊥) λ o → Fin (length (arity o)))
        (λ sort → ⊎.elim (λ v ()) (λ o p → arity o ! p))
        sortOut

    toRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut → RepTermF X sortOut
    toRepTermF X sortOut (varF v) = node (inl v) (λ ())
    toRepTermF X sortOut (astF (term1 o args)) =
      node (inr o) λ p → toRepTermF X (arity o ! p) (args p)

    fromRepTermF : (X : MType) (sortOut : Sort) → RepTermF X sortOut → TermF X sortOut
    fromRepTermF X sortOut (node (inl v) u) = varF v
    fromRepTermF X sortOut (node (inr o) args) = astF (term1 o λ p → fromRepTermF X (arity o ! p) (args p))
  
    fromToRepTermF : (X : MType) (sortOut : Sort) (t : TermF X sortOut)
      → fromRepTermF X sortOut (toRepTermF X sortOut t) ≡ t
    fromToRepTermF X sortOut (varF v) = refl
    fromToRepTermF X sortOut (astF (term1 o args)) i =
      astF (term1 o λ p → fromToRepTermF X (arity o ! p) (args p) i)

    toFromRepTermF : (X : MType) (sortOut : Sort) (rt : RepTermF X sortOut)
      → toRepTermF X sortOut (fromRepTermF X sortOut rt) ≡ rt
    toFromRepTermF X sortOut (node (inl v) u) = cong (node (inl v)) (funExt (λ ()))
    toFromRepTermF X sortOut (node (inr o) args) i =
      node (inr o) (λ p → toFromRepTermF X (arity o ! p) (args p) i)

    isoRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut ≅ RepTermF X sortOut
    fun (isoRepTermF X sortOut) = toRepTermF X sortOut
    inv (isoRepTermF X sortOut) = fromRepTermF X sortOut
    rightInv (isoRepTermF X sortOut) = toFromRepTermF X sortOut
    leftInv (isoRepTermF X sortOut) = fromToRepTermF X sortOut

    pathRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut ≡ RepTermF X sortOut
    pathRepTermF X sortOut = ua (isoToEquiv (isoRepTermF X sortOut))
  
    isSetRepTermF : (msetX : MSet) (sortOut : Sort) → isSet (RepTermF (mtyp msetX) sortOut)
    isSetRepTermF msetX sortOut = isOfHLevelSuc-IW 1 (λ sort → isSet⊎ (str (msetX sort)) isSetOperation) sortOut
  
    isSetTermF msetX sortOut = subst⁻ isSet (pathRepTermF (mtyp msetX) sortOut) (isSetRepTermF msetX sortOut)

open Presentation {{...}} public
