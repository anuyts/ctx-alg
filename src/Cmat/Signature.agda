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
    isGroupoidMode : isGroupoid Mode
    CustomRHS : Mode → Type
    isGroupoidCustomRHS : ∀ {m} → isGroupoid (CustomRHS m)

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

  isGroupoidRHS : isGroupoid (RHS m)
  isGroupoidRHS = {!!}

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

    isGroupoidRepJud : isGroupoid RepJud
    isGroupoidRepJud = isOfHLevelΣ 3 isGroupoidMode λ m → isOfHLevelΣ 3 (isSet→isGroupoid isSetCtx) (λ _ → isGroupoidRHS)

  isGroupoidJud : isGroupoid Jud
  isGroupoidJud = isOfHLevelRetractFromIso 3 isoRepJud isGroupoidRepJud

module _ (cmatsig : CmatSignature) where

  open CmatSignature

  data OpenCustomRHS (m : Mode cmatsig) : Type where
    custom : CustomRHS cmatsig m → OpenCustomRHS m
    ctx : Ctx cmatsig m → OpenCustomRHS m

  {- The signature of the open translation.
  -}
  cmatsigOpen : Mode cmatsig → CmatSignature
  catModeJunctor (cmatsigOpen m) = catModeJunctor cmatsig
  pshCtx (cmatsigOpen m) =
    funcComp (HomFunctor (catModeJunctor cmatsig)) (rinj (catModeJunctor cmatsig ^op) (catModeJunctor cmatsig) m)
  isGroupoidMode (cmatsigOpen m) = isGroupoidMode cmatsig
  CustomRHS (cmatsigOpen m) = RHS cmatsig
  isGroupoidCustomRHS (cmatsigOpen m) = isGroupoidRHS cmatsig

  open MatSignature

  {- The signature of the MAT translation.
  -}
  matsig : MatSignature
  Sort matsig = Jud cmatsig
  isGroupoidSort matsig = isGroupoidJud cmatsig

open CmatSignature {{...}} public
