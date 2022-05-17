{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Reflection.RecordEquiv

open import Mat.Signature

module Cmat.Signature where

open Category
open Functor

{- Instantiators should see to it that the mode can be inferred
   from the type of contexts/customRHSs. -}
record CmatSignature : Type where
  no-eta-equality
  field
    catModeJunctor : Category _ _
    pshCtx : Functor catModeJunctor (SET _)

  Mode : Type
  Mode = ob catModeJunctor

  field
    CustomRHS : Mode → Type
    isSetCustomRHS : ∀ {m} → isSet (CustomRHS m)

  private
    variable
      m n : Mode

  Junctor : Mode → Mode → Type
  Junctor = Hom[_,_] catModeJunctor

  isSetJunctor : isSet (Junctor m n)
  isSetJunctor = isSetHom catModeJunctor

  Ctx : Mode → Type
  Ctx m = fst (F-ob pshCtx m)

  isSetCtx : isSet (Ctx m)
  isSetCtx {m} = snd (F-ob pshCtx m)

  _⦊_ : Ctx m → Junctor m n → Ctx n
  Γ ⦊ Ψ = F-hom pshCtx Ψ Γ

  data RHS (m : Mode) : Type where
    custom : CustomRHS m → RHS m
    ctx : Ctx m → RHS m
    jhom : ∀ {n} → (Ψ Φ : Junctor m n) → RHS m

  isSetRHS : isSet (RHS m)
  isSetRHS = {!!}

  record Jud : Type where
    constructor _⊩_
    field
      {jud'mode} : Mode
      jud'ctx : Ctx jud'mode
      jud'rhs : RHS jud'mode

  pattern _⊢_ Γ crhsT = Γ ⊩ custom crhsT

  module _ where
    open _≅_

    RepJud : Type
    RepJud = Σ[ m ∈ Mode ] Σ[ Γ ∈ Ctx m ] RHS m

    private
      unquoteDecl isoRepJud' = declareRecordIsoΣ isoRepJud' (quote Jud)

    isoRepJud : Jud ≅ RepJud
    isoRepJud = isoRepJud'

    isSetRepJud : isSet RepJud
    isSetRepJud = isOfHLevelΣ 2 {!isSetMode!} {!!}

  isSetJud : isSet Jud
  isSetJud = isOfHLevelRetractFromIso 2 isoRepJud isSetRepJud

module _ (cmatsig : CmatSignature) where
  open CmatSignature

  {- The signature of the open translation.
  -}
  cmatsigOpen : Mode cmatsig → CmatSignature
  catModeJunctor (cmatsigOpen m) = catModeJunctor cmatsig
  pshCtx (cmatsigOpen m) =
    funcComp (HomFunctor (catModeJunctor cmatsig)) (rinj (catModeJunctor cmatsig ^op) (catModeJunctor cmatsig) m)
  CustomRHS (cmatsigOpen m) = RHS cmatsig
  isSetCustomRHS (cmatsigOpen m) = isSetRHS cmatsig

  open Signature

  {- The signature of the MAT translation.
  -}
  matsig : Signature
  Sort matsig = Jud cmatsig
  isSetSort matsig = isSetJud cmatsig

open CmatSignature {{...}} public
