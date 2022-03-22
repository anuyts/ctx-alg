{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.List
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

  Precarrier : Type
  Precarrier = Sort → hSet _

  catPrecarrier : Category _ _
  catPrecarrier = ΠC Sort λ _ → SET _

open Signature {{...}} public
