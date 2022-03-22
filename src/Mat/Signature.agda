{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.List

module Mat.Signature where

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

  --catPrecarrier : 

open Signature {{...}} public
