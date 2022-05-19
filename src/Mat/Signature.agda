{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.List.FinData renaming (lookup to _!_)
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
    isSetSort : isSet Sort

  Arity : Type
  Arity = List Sort
  isSetArity : isSet Arity
  isSetArity = isOfHLevelList 0 isSetSort

  MType : Type
  MType = Sort → Type

  MSet : Type
  MSet = Sort → hSet _

  arity2mset : Arity → MSet
  fst (arity2mset arity sort) = Σ[ p ∈ Fin (length arity) ] arity ! p ≡ sort
  snd (arity2mset arity sort) (p , e) (p' , e') e1 e2 = cong ΣPathP (ΣPathP (
    isSetFin _ _ _ _ ,
    isProp→SquareP (λ i j → isSetSort _ _) _ _ _ _
    ))

  mtyp : MSet → MType
  mtyp prec sort = typ (prec sort)

  catMSet : Category _ _
  catMSet = ΠC Sort λ _ → SET _

  -- I'd prefer a dependent list
  Arguments : MType → Arity → Type
  Arguments X arity = (p : Fin (length arity)) → X (arity ! p)

  isSetArguments : ∀ precarrier arity → isSet (Arguments (mtyp precarrier) arity)
  isSetArguments precarrier arity = isOfHLevelΠ 2 λ p → str (precarrier (arity ! p))

  msetEmpty : MSet
  msetEmpty sort = ⊥ , (λ ())

  isInitial-msetEmpty : isInitial catMSet msetEmpty
  fst (isInitial-msetEmpty msetX) sort ()
  snd (isInitial-msetEmpty msetX) f = funExt λ sort → funExt (λ ())
