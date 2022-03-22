{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
--open import Cubical.Categories.Category

module Cmat.Signature where

record Signature : Type where
  no-eta-equality
  field
    Mode : Set
    isSetMode : isSet Mode
    Ty : Mode → Set
    isSetTy : (m : Mode) → isSet (Ty m)

open Signature {{...}} public
