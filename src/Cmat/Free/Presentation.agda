{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinData
open import Cubical.Categories.Category

open import Mat.Signature
open import Mat.Free.Presentation
open import Mat.Free.Term
open import Mat.Presentation
open import Cmat.Signature

module Cmat.Free.Presentation where

record FreeCmat (cmatsig : CmatSignature) : Type where
  open CmatSignature cmatsig
  open CmatFoundation

  -- Basically a judgement whose context is the identity junctor:
  -- ◇ ⊩ rhs @ m
  LoneRHS : Mode → Type
  LoneRHS m = RHS (cmatfndOpen m) m

  field
    CustomOperation : ∀ {m} → LoneRHS m → Type
    isSetCustomOperation : ∀ {m} {rhs : LoneRHS m} → isSet (CustomOperation rhs)
    arityCustom : ∀ {m} {rhs : LoneRHS m} → CustomOperation rhs → CArity m

  private
    variable m n p q : Mode

  data Operation : LoneRHS m → Type where
    custom : ∀ {m} {rhs : LoneRHS m} → CustomOperation rhs → Operation rhs
    id-jhom : ∀ {m n} {Φ : Junctor m n} → Operation (jhom Φ Φ)
    comp-jhom : ∀ {m n} {Φ Ψ Ξ : Junctor m n} → Operation (jhom Φ Ξ)
    whiskerL : ∀ {m n p} (Ξ : Junctor m n) {Φ Ψ : Junctor n p} → Operation (jhom (Ξ ⦊ Φ) (Ξ ⦊ Ψ))
    whiskerR : ∀ {m n p} {Φ Ψ : Junctor m n} (Ξ : Junctor n p) → Operation (jhom (Φ ⦊ Ξ) (Ψ ⦊ Ξ))
    -- whiskerL t ∘ whiskerR s = whiskerR s ∘ whiskerL (t [ Γ.s ])
    -- whiskerL (whiskerR t) = whiskerR (whiskerL t)
    -- whiskerL respects id-jhom and comp-jhom
    -- whiskerR respects id-jhom and comp-jhom
    -- whiskerL respects ◇ and ⦊
    -- whiskerR respects ◇ and ⦊

  isSetOperation : ∀ {m} {rhs : LoneRHS m} → isSet (Operation rhs)
  isSetOperation = {!!} -- via reflection

  arity : ∀ {m} {rhs : LoneRHS m} → Operation rhs → CArity m
  arity (custom o) = arityCustom o
  arity id-jhom = []
  arity (comp-jhom {m} {n} {Φ} {Ψ} {Ξ}) = (◇ ⊩ jhom Φ Ψ) ∷ (◇ ⊩ jhom Ψ Ξ) ∷ []
  arity (whiskerL {m} {n} {p} Ξ {Φ} {Ψ}) = (Ξ ⊩ jhom Φ Ψ) ∷ []
  arity (whiskerR {m} {n} {p} {Φ} {Ψ} Ξ) = (◇ ⊩ jhom Φ Ψ) ∷ []

  -- The cold translation
  module _ (cmatfnd : CmatFoundation) where

    open MatSignature (matsigClosed cmatfnd)
    private
      module F = CmatFoundation cmatfnd

    data OperationCold : Jud cmatfnd → Type where
      inctx : ∀ {m} {Γ : F.Ctx m} {rhs : LoneRHS m} → (o : Operation rhs)
        → OperationCold (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
        -- → OperationCold (translateJudClosed cmatfnd Γ (◇ ⊩ rhs))
      idsub : ∀ {m} {Γ : F.Ctx m} → OperationCold (Γ ⊩ sub Γ)
      --compsub : ∀ {m} {Γ Δ Θ : F.Ctx m} → OperationCold (Γ ⊩ sub Θ)
      -- The following two involve a delayed substitution from Ω
      mixWhiskerL : ∀ {n p} {Ω : F.Ctx p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → OperationCold (Ω ⊩ sub (Θ F.:⦊ Ψ))
      mixWhiskerR : ∀ {n p} {Ω : F.Ctx p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → OperationCold (Ω ⊩ sub (Δ F.:⦊ Ξ))
      -- mixWhiskerL t ∘ mixWhiskerR s = mixWhiskerR s ∘ mixWhiskerL (t [ Γ.s ])
      -- mixWhiskerL (whiskerR t) = mixWhiskerR (mixWhiskerL t)
      -- mixWhiskerL respects id-jhom and comp-jhom
      -- mixWhiskerR respects idsub and compsub
      -- mixWhiskerL respects :⦊
      -- mixWhiskerR respects ◇ and ⦊

    isSetOperationCold : ∀ {J} → isSet (OperationCold J)
    isSetOperationCold = {!!} -- via reflection

    arityCold : ∀ {J} → OperationCold J → Arity
    arityCold (inctx {m} {Γ} {rhs} o) = translateArityClosed cmatfnd Γ (arity o)
    arityCold idsub = []
    --arityCold (compsub {m} {Γ} {Δ} {Θ}) = (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
    arityCold (mixWhiskerL {n} {p} {Ω} Θ {Φ} {Ψ}) = (Θ ⊩ jhom Φ Ψ) ∷ (Ω ⊩ sub (Θ F.:⦊ Φ)) ∷ []
    arityCold (mixWhiskerR {n} {p} {Ω} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ)    ∷ (Ω ⊩ sub (Γ F.:⦊ Ξ)) ∷ []

    fmatCold : FreeMat (matsigClosed cmatfnd)
    FreeMat.Operation fmatCold = OperationCold
    FreeMat.isSetOperation fmatCold = isSetOperationCold
    FreeMat.arity fmatCold = arityCold

    open MatEqTheory
    open TermF fmatCold

    -- AxiomColdTmsub would be empty
    -- AxiomColdCat would be empty

  -- The hot translation
  module _ (cmatfnd : CmatFoundation) where

    open MatSignature (matsigClosed cmatfnd)
    private
      module F = CmatFoundation cmatfnd

    data OperationHot : Jud cmatfnd → Type where
      cold : ∀ {J} → OperationCold cmatfnd J → OperationHot J
      tmsub : ∀ {m} {Γ Δ : F.Ctx m} {rhs : RHS cmatfnd m} → OperationHot (Γ ⊩ rhs)

    isSetOperationHot : ∀ {J : Jud cmatfnd} → isSet (OperationHot J)
    isSetOperationHot = {!!}

    arityHot : ∀ {J : Jud cmatfnd} → OperationHot J → Arity
    arityHot (cold o) = arityCold cmatfnd o
    arityHot (tmsub {m} {Γ} {Δ} {rhs}) = (Δ ⊩ rhs) ∷ (Γ ⊩ sub Δ) ∷ []

    fmatHot : FreeMat (matsigClosed cmatfnd)
    FreeMat.Operation fmatHot = OperationHot
    FreeMat.isSetOperation fmatHot = isSetOperationHot
    FreeMat.arity fmatHot = arityHot

    ophomCold→Hot : OpHom (fmatCold cmatfnd) fmatHot
    OpHom.F-operation ophomCold→Hot = cold
    OpHom.F-arity ophomCold→Hot o = refl

    open MatEqTheory
    open TermF fmatHot

    pattern _[_]1 t σ = tmsub $1 (t ∷ σ ∷ [])
    infixl 7 _[_]1

    data AxiomHot : Jud cmatfnd → Type where
      tmsub-inctx : ∀ {m} {Γ Δ : F.Ctx m} {rhs : LoneRHS m} (o : Operation rhs)
        → AxiomHot (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
      tmsub-mixWhiskerL : ∀ {n p} {Ω' Ω : F.Ctx p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → AxiomHot (Ω' ⊩ sub (Θ F.:⦊ Ψ))
      tmsub-mixWhiskerR : ∀ {n p} {Ω' Ω : F.Ctx p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → AxiomHot (Ω' ⊩ sub (Δ F.:⦊ Ξ))
      tmsub-lunit : ∀ {Γ Δ : F.Ctx m} → AxiomHot (Γ ⊩ sub Δ)
      tmsub-runit : ∀ {Γ : F.Ctx m} {rhs : F.RHS m} → AxiomHot (Γ ⊩ rhs)
      tmsub-assoc : ∀ {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} → AxiomHot (Γ ⊩ rhs)

    arityAxiomHot : ∀{J} → AxiomHot J → Arity
    arityAxiomHot (tmsub-inctx {m} {Γ} {Δ} {rhs} o) = (Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o)
    arityAxiomHot (tmsub-mixWhiskerL {n} {p} {Ω'} {Ω} Θ {Φ} {Ψ}) = (Θ ⊩ jhom Φ Ψ) ∷ (Ω ⊩ sub (Θ F.:⦊ Φ)) ∷ (Ω' ⊩ sub Ω) ∷ []
    arityAxiomHot (tmsub-mixWhiskerR {n} {p} {Ω'} {Ω} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ)    ∷ (Ω ⊩ sub (Γ F.:⦊ Ξ)) ∷ (Ω' ⊩ sub Ω) ∷ []
    arityAxiomHot (tmsub-lunit {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomHot (tmsub-runit {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomHot (tmsub-assoc {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []

    lhsAxiomHot rhsAxiomHot : ∀ {J} → (axiom : AxiomHot J)
      → TermF (mtyp (arity2mset (arityAxiomHot axiom))) J
    lhsAxiomHot (tmsub-inctx {m} {Γ} {Δ} {rhs} o) =
      (cold (inctx o) $1 tabulateOverLookup (arityCold cmatfnd (inctx o)) (arvarF ∘ suc)) [ arvarF zero ]1
    lhsAxiomHot (tmsub-mixWhiskerL {n} {p} {Ω'} {Ω} Θ {Φ} {Ψ}) =
      (cold (mixWhiskerL Θ) $1 arvarF zero ∷ arvarF one ∷ []) [ arvarF two ]1
    lhsAxiomHot (tmsub-mixWhiskerR {n} {p} {Ω'} {Ω} {Γ} {Δ} Ξ) =
      (cold (mixWhiskerR Ξ) $1 arvarF zero ∷ arvarF one ∷ []) [ arvarF two ]1
    lhsAxiomHot tmsub-lunit = (cold idsub $1 []) [ arvarF zero ]1
    lhsAxiomHot tmsub-runit = arvarF zero [ cold idsub $1 [] ]1
    lhsAxiomHot tmsub-assoc = arvarF zero [ arvarF one ]1 [ arvarF two ]1
    rhsAxiomHot (tmsub-inctx {m} {Γ} {Δ} {rhs} o) =
      cold (inctx o) $1 mapOverSpan
        {B = TermF (mtyp (arity2mset ((Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o))))}
        {B' = TermF (mtyp (arity2mset (arityAxiomHot (tmsub-inctx o))))}
        (translateJudClosed cmatfnd Δ)
        (translateJudClosed cmatfnd Γ)
        (λ J x → x [ cold (mixWhiskerR _) $1 arvarF zero ∷ (cold idsub $1 []) ∷ [] ]1)
        (arity o)
        (tabulateOverLookup (arityCold cmatfnd (inctx o)) (arvarF ∘ suc))
    rhsAxiomHot (tmsub-mixWhiskerL {n} {p} {Ω'} {Ω} Θ {Φ} {Ψ}) =
      cold (mixWhiskerL Θ) $1 arvarF zero ∷ (arvarF one [ arvarF two ]1) ∷ []
    rhsAxiomHot (tmsub-mixWhiskerR {n} {p} {Ω'} {Ω} {Γ} {Δ} Ξ) =
      cold (mixWhiskerR Ξ) $1 arvarF zero ∷ (arvarF one [ arvarF two ]1) ∷ []
    rhsAxiomHot tmsub-lunit = arvarF zero
    rhsAxiomHot tmsub-runit = arvarF zero
    rhsAxiomHot tmsub-assoc = arvarF zero [ arvarF one [ arvarF two ]1 ]1

    eqTheoryHot : MatEqTheory fmatHot
    Axiom eqTheoryHot = AxiomHot
    msetArity eqTheoryHot = arity2mset ∘ arityAxiomHot
    lhs eqTheoryHot = lhsAxiomHot
    rhs eqTheoryHot = rhsAxiomHot

    matHot : Mat (matsigClosed cmatfnd)
    Mat.getFreeMat matHot = fmatHot
    Mat.getMatEqTheory matHot = eqTheoryHot
