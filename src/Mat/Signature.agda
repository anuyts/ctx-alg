{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.TypeProduct
open import Cubical.Categories.Instances.Sets

module Mat.Signature where

open Category

record Signature : Type where
  no-eta-equality
  field
    Sort : Type
    isSetSort : isSet Sort

  Arity : Type
  Arity = List Sort
  isSetArity : isSet Arity
  isSetArity = isOfHLevelList 0 isSetSort

  MType : Type
  MType = Sort → Type

  MSet : Type
  MSet = Sort → hSet _

  mtyp : MSet → MType
  mtyp prec sort = typ (prec sort)

  catMSet : Category _ _
  catMSet = ΠC Sort λ _ → SET _

  Arguments : MType → Arity → Type
  Arguments X arity = (p : Fin (length arity)) → X (arity ! p)

  isSetArguments : ∀ precarrier arity → isSet (Arguments (mtyp precarrier) arity)
  isSetArguments precarrier arity = isOfHLevelΠ 2 λ p → str (precarrier (arity ! p))

open Signature {{...}} public
