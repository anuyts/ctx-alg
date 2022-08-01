{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude

open import Mat.Signature
open import Mat.Free.Presentation
open import Mat.Free.Term
open import Mat.Presentation
open import Mat.Term
open import Cmat.Signature
open import Cmat.Free.Presentation

module Cmat.Free.SameSyntax where

-- The common signature
module CommonSignature {cmatsig : CmatSignature} (cmatfnd : CmatSignature.CmatFoundation cmatsig) where

  open CmatSignature cmatsig
  open CmatFoundation cmatfnd

  matsig : MatSignature
  matsig = matsigClosed cmatfnd

  open MatSignature matsig

  {- Let X and S be multisorted sets of signature matsig.
     Then S defines a category of contexts and substitutions.
     We define the free mode- and type-indexed S-presheaf over X.
     This is akin to Fiore & Szamozvancev's monoidal product S ⊙ X,
     except that we don't assume a priori that S and X are renamable.
     Hence, we need not take an end.
  -}
  data FreeTypedPsh (S X : MType) : MType where
    _[_]Free : ∀ {m : Mode} {Γ Δ : Ctx m} {rhs : RHS m} → S (Γ ⊩ sub Δ) → X (Δ ⊩ rhs) → FreeTypedPsh S X (Γ ⊩ rhs)

  msetFreeTypedPsh : (msetS msetX : MSet) → MSet
  fst (msetFreeTypedPsh msetS msetX J) = FreeTypedPsh (mtyp msetS) (mtyp msetX) J
  snd (msetFreeTypedPsh msetS msetX J) = {!!}

module SameSyntax {cmatsig : CmatSignature} (cmatfnd : CmatSignature.CmatFoundation cmatsig) (fcmat : FreeCmat cmatsig) where

  open CmatSignature cmatsig
  open CmatFoundation cmatfnd
  open CommonSignature cmatfnd
  open MatSignature matsig
  open TermF {matsig}
  open FreeCmat fcmat

  module _ (msetX : MSet) where

    TermHot : MType
    TermHot = TermQ (matHotTmsub cmatfnd) (mtyp msetX)

    msetHot : MSet
    msetHot = msetTermQ (matHotTmsub cmatfnd) msetX

    private
      testHot : TermHot ≡ mtyp msetHot
      testHot = refl

    TermCold : MType
    TermCold = TermF (fmatCold cmatfnd) (FreeTypedPsh TermHot (mtyp msetX))

    msetCold : MSet
    msetCold = msetTermF (fmatCold cmatfnd) (msetFreeTypedPsh msetHot msetX)

    private
      testCold : TermCold ≡ mtyp msetCold
      testCold = refl
