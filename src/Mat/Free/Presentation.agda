{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.List.Dependent
open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Instances.FunctorAlgebras

open import Mat.Signature

module Mat.Free.Presentation where

open _≅_
open Category renaming (_∘_ to _⊚_)
open Functor

-- Type of free MAT presentations (MAT presentations without equations)
record FreeMat (matsig : MatSignature) : Type where
  open MatSignature matsig

  field
    Operation : Sort → Type
    isSetOperation : {sortOut : Sort} → isSet (Operation sortOut)
    arity : ∀ {sortOut} → Operation sortOut → Arity

  -- SyntaxQ functor
  record Term1 (X : MType) (sortOut : Sort) : Type where
    inductive
    constructor term1
    field
      operation : Operation sortOut
      arguments : Arguments X (arity operation)
  open Term1

  mapTerm1 : ∀ {X Y : MType} (f : (sort : Sort) → X sort → Y sort) → (sort : Sort) → Term1 X sort → Term1 Y sort
  operation (mapTerm1 f sort t) = operation t
  arguments (mapTerm1 f sort t) = mapOverIdfun f (arity (operation t)) (arguments t)

  mapTerm1-id : ∀ {X : MType} → (mapTerm1 (λ sort → idfun (X sort))) ≡ (λ sort → idfun (Term1 X sort))
  operation (mapTerm1-id i sort t) = operation t
  arguments (mapTerm1-id i sort t) = mapOverIdfun-idfun (arity (operation t)) i (arguments t)

  mapTerm1-∘ : ∀ {X Y Z : MType}
    (g : (sort : Sort) → Y sort → Z sort)
    (f : (sort : Sort) → X sort → Y sort)
    → mapTerm1 (λ sort → g sort ∘ f sort) ≡ (λ sort → mapTerm1 g sort ∘ mapTerm1 f sort)
  operation (mapTerm1-∘ g f i sort t) = operation t
  arguments (mapTerm1-∘ g f i sort t) = mapOverIdfun-∘ g f (arity (operation t)) i (arguments t)

  -- Term1 is really a Σ-type
  module _ where
    RepTerm1 : (X : MType) (sortOut : Sort) → Type
    RepTerm1 X sortOut = Σ[ o ∈ Operation sortOut ] Arguments X (arity o)

    isoRepTerm1 : (X : MType) (sortOut : Sort)
      → Term1 X sortOut ≅ RepTerm1 X sortOut
    fun (isoRepTerm1 X sortOut) t = operation t , arguments t
    inv (isoRepTerm1 X sortOut) (o , args) = term1 o args
    rightInv (isoRepTerm1 X sortOut) (o , args) = refl
    operation (leftInv (isoRepTerm1 X sortOut) t i) = operation t
    arguments (leftInv (isoRepTerm1 X sortOut) t i) = arguments t

    pathRepTerm1 : (X : MType) (sortOut : Sort)
      → Term1 X sortOut ≡ RepTerm1 X sortOut
    pathRepTerm1 X sortOut = ua (isoToEquiv (isoRepTerm1 X sortOut))

    isSetRepTerm1 : (msetX : MSet) (sortOut : Sort) → isSet (RepTerm1 (mtyp msetX) sortOut)
    isSetRepTerm1 msetX sortOut =
      isOfHLevelΣ 2 isSetOperation (λ o → isSetArguments msetX (arity o))

  isSetTerm1 : (msetX : MSet) (sortOut : Sort) →  isSet (Term1 (mtyp msetX) sortOut)
  isSetTerm1 msetX sortOut =
    subst⁻ isSet (pathRepTerm1 (mtyp msetX) sortOut) (isSetRepTerm1 msetX sortOut)

  -- Term1 as an action on MSets
  msetTerm1 : MSet → MSet
  fst (msetTerm1 mset sortOut) = Term1 (mtyp mset) sortOut
  snd (msetTerm1 mset sortOut) = isSetTerm1 mset sortOut

  -- Term1 as a functor on catMSet
  ftrTerm1 : Functor catMSet catMSet
  F-ob ftrTerm1 = msetTerm1
  F-hom ftrTerm1 {x = msetX} {y = msetY} = mapTerm1
  F-id ftrTerm1 {x = msetX} = mapTerm1-id
  F-seq ftrTerm1 {x = msetX} {y = msetY} {z = precZ} f g = mapTerm1-∘ g f

  -- ModelQs of the MAT presentation are algebras of ftrTerm1
  catModel1 : Category ℓ-zero ℓ-zero
  catModel1 = AlgebrasCategory ftrTerm1

  Model1 : Type ℓ-zero
  Model1 = ob catModel1

  Model1Hom : (m1A m1B : Model1) → Type ℓ-zero
  Model1Hom = Hom[_,_] catModel1

  -- Forgetful functor sending models to their carrier
  ftrForgetModel1 : Functor catModel1 catMSet
  ftrForgetModel1 = ForgetAlgebra ftrTerm1

module _ {matsig : MatSignature} (fmat1 fmat2 : FreeMat matsig) where

  open MatSignature matsig
  open FreeMat
  open Term1

  record OpHom : Type where
    field
      F-operation : ∀ {sort} → Operation fmat1 sort → Operation fmat2 sort
      F-arity : ∀ {sort} (o : Operation fmat1 sort) → arity fmat2 (F-operation o) ≡ arity fmat1 o
  open OpHom

  opmapTerm1 : OpHom → ∀ {X} sort → Term1 fmat1 X sort → Term1 fmat2 X sort
  operation (opmapTerm1 ophom {X} sort t) = F-operation ophom (operation t)
  arguments (opmapTerm1 ophom {X} sort t) = subst (Arguments X) (sym (F-arity ophom (operation t))) (arguments t)
