{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.List.Dependent
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Initial

module Mat.Signature where

open Category

-- A MAT Signature is like a type for MATs: it specifies the set of Sorts.
record MatSignature : Type where
  no-eta-equality
  field
    Sort : Type
    isGroupoidSort : isGroupoid Sort

  Arity : Type
  Arity = List Sort
  isGroupoidArity : isGroupoid Arity
  isGroupoidArity = isOfHLevelList 1 isGroupoidSort

  -- sort-indexed type
  MType : Type
  MType = Sort → Type

  -- sort-indexed set
  MSet : Type
  MSet = Sort → hSet _

  -- indexed set of well-typed variables
  arity2mset : Arity → MSet
  fst (arity2mset arity sort) = Σ[ p ∈ Fin (length arity) ] arity ! p ≡ sort
  snd (arity2mset arity sort) = isSetΣ isSetFin λ p → isOfHLevelPath' 2 isGroupoidSort _ _

  mtyp : MSet → MType
  mtyp mset sort = typ (mset sort)

  -- category of indexed sets
  catMSet : Category _ _
  catMSet = ΠC Sort λ _ → SET _

  Arguments : MType → Arity → Type
  Arguments X arity = ListP X arity

  isSetArguments : ∀ precarrier arity → isSet (Arguments (mtyp precarrier) arity)
  isSetArguments precarrier arity = isOfHLevelSucSuc-ListP 0 (λ sort → snd (precarrier sort))

  -- initial indexed set
  msetEmpty : MSet
  msetEmpty sort = ⊥ , (λ ())

  isInitial-msetEmpty : isInitial catMSet msetEmpty
  fst (isInitial-msetEmpty msetX) sort ()
  snd (isInitial-msetEmpty msetX) f = funExt λ sort → funExt (λ ())
