{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool
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

  -- The hot/cold translation
  module _ (cmatfnd : CmatFoundation) where

    open MatSignature (matsigClosed cmatfnd)
    private
      module F = CmatFoundation cmatfnd

    data OperationClosed : (heat : Heat) → Jud cmatfnd → Type where
      inctx : ∀ {heat} {m} {Γ : F.Ctx m} {rhs : LoneRHS m} → (o : Operation rhs)
        → OperationClosed heat (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
        -- → OperationClosed heat (translateJudClosed cmatfnd Γ (◇ ⊩ rhs))
      idsub : ∀ {heat} {m} {Γ : F.Ctx m} → OperationClosed heat (Γ ⊩ sub Γ)
      --compsub : ∀ {m} {Γ Δ Θ : F.Ctx m} → OperationClosed heat (Γ ⊩ sub Θ)
      -- The following two involve a delayed substitution from Ω
      mixWhiskerL : ∀ {heat} {n p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → OperationClosed heat (Θ F.:⦊ Φ ⊩ sub (Θ F.:⦊ Ψ))
      mixWhiskerR : ∀ {heat} {n p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → OperationClosed heat (Γ F.:⦊ Ξ ⊩ sub (Δ F.:⦊ Ξ))
      -- mixWhiskerL t ∘ mixWhiskerR s = mixWhiskerR s ∘ mixWhiskerL (t [ Γ.s ])
      -- mixWhiskerL (whiskerR t) = mixWhiskerR (mixWhiskerL t)
      -- mixWhiskerL respects id-jhom and comp-jhom
      -- mixWhiskerR respects idsub and compsub
      -- mixWhiskerL respects :⦊
      -- mixWhiskerR respects ◇ and ⦊
      gensub : ∀ {heat} {m} {Γ Δ : F.Ctx m} {rhs : F.RHS m}
        → {{u : F.Substitutable heat rhs}} → OperationClosed heat (Γ ⊩ rhs)

    pattern tmsub = gensub {hot} {{tt}}
    pattern compsub = gensub {cold} {{tt}}

    OperationCold = OperationClosed cold
    OperationHot = OperationClosed hot

    isSetOperationClosed : ∀ {heat} {J} → isSet (OperationClosed heat J)
    isSetOperationClosed = {!!} -- via reflection

    arityClosed : ∀ {heat} {J} → OperationClosed heat J → Arity
    arityClosed (inctx {heat} {m} {Γ} {rhs} o) = translateArityClosed cmatfnd Γ (arity o)
    arityClosed idsub = []
    arityClosed (mixWhiskerL {heat} {n} {p} Θ {Φ} {Ψ}) = (Θ ⊩ jhom Φ Ψ) ∷ []
    arityClosed (mixWhiskerR {heat} {n} {p} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ)    ∷ []
    arityClosed (gensub {heat} {m} {Γ} {Δ} {rhs}) = (Δ ⊩ rhs) ∷ (Γ ⊩ sub Δ) ∷ []

    fmatClosed : Heat → FreeMat (matsigClosed cmatfnd)
    FreeMat.Operation (fmatClosed heat) = OperationClosed heat
    FreeMat.isSetOperation (fmatClosed heat) = isSetOperationClosed
    FreeMat.arity (fmatClosed heat) = arityClosed

    fmatCold = fmatClosed cold
    fmatHot = fmatClosed hot

    ophomCold→Hot : OpHom fmatCold fmatHot
    OpHom.F-operation ophomCold→Hot (inctx o) = inctx o
    OpHom.F-operation ophomCold→Hot idsub = idsub
    OpHom.F-operation ophomCold→Hot (mixWhiskerL Θ) = mixWhiskerL Θ
    OpHom.F-operation ophomCold→Hot (mixWhiskerR Ξ) = mixWhiskerR Ξ
    OpHom.F-operation ophomCold→Hot (gensub {cold} {m} {Γ} {Δ} {rhs}) = gensub {hot} {m} {Γ} {Δ} {rhs}
    OpHom.F-arity ophomCold→Hot (inctx o) = refl
    OpHom.F-arity ophomCold→Hot idsub = refl
    OpHom.F-arity ophomCold→Hot (mixWhiskerL Θ) = refl
    OpHom.F-arity ophomCold→Hot (mixWhiskerR Ξ) = refl
    OpHom.F-arity ophomCold→Hot (gensub) = refl

    open MatEqTheory
    private
      module TermFClosed (heat : Heat) = TermF (fmatClosed heat)
    open TermFClosed

    pattern _[_]1 t σ = gensub $1 (t ∷ σ ∷ [])
    infixl 7 _[_]1

    data AxiomClosed : Heat → Jud cmatfnd → Type where
      gensub-inctx : ∀ {heat} {m} {Γ Δ : F.Ctx m} {rhs : LoneRHS m}
        {{u : Substitutable _ heat (translateRHSClosedEmptyContext cmatfnd rhs)}} (o : Operation rhs)
        → AxiomClosed heat (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
      gensub-lunit : ∀ {heat} {Γ Δ : F.Ctx m} → AxiomClosed heat (Γ ⊩ sub Δ)
      gensub-runit : ∀ {heat} {Γ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable heat rhs}} → AxiomClosed heat (Γ ⊩ rhs)
      gensub-assoc : ∀ {heat} {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable heat rhs}} → AxiomClosed heat (Γ ⊩ rhs)

    arityAxiomClosed : ∀ {heat} {J} → AxiomClosed heat J → Arity
    arityAxiomClosed (gensub-inctx {heat} {m} {Γ} {Δ} {rhs} o) = (Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o)
    arityAxiomClosed (gensub-lunit {heat} {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomClosed (gensub-runit {heat} {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomClosed (gensub-assoc {heat} {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []

    lhsAxiomClosed rhsAxiomClosed : ∀ {heat} {J} → (axiom : AxiomClosed heat J)
      → TermF heat (mtyp (arity2mset (arityAxiomClosed axiom))) J
    lhsAxiomClosed (gensub-inctx {heat} {m} {Γ} {Δ} {rhs} o) =
      (inctx o $1 tabulateOverLookup (arityClosed {heat} (inctx o)) (arvarF _ ∘ suc)) [ arvarF _ zero ]1
    lhsAxiomClosed gensub-lunit = (idsub $1 []) [ arvarF _ zero ]1
    lhsAxiomClosed gensub-runit = arvarF _ zero [ idsub $1 [] ]1
    lhsAxiomClosed gensub-assoc = arvarF _ zero [ arvarF _ one ]1 [ arvarF _ two ]1
    rhsAxiomClosed (gensub-inctx {heat} {m} {Γ} {Δ} {rhs} o) =
      inctx o $1 mapOverSpan
        {B = TermF heat (mtyp (arity2mset ((Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o))))}
        {B' = TermF heat (mtyp (arity2mset (arityAxiomClosed {heat} (gensub-inctx o))))}
        (translateJudClosed cmatfnd Δ)
        (translateJudClosed cmatfnd Γ)
        (λ J x → {!x [ mixWhiskerR _ $1 arvarF _ zero ∷ [] ]1!})
        (arity o)
        {!tabulateOverLookup (arityCold cmatfnd (inctx o)) (arvarF _ ∘ suc)!}
    rhsAxiomClosed gensub-lunit = arvarF _ zero
    rhsAxiomClosed gensub-runit = arvarF _ zero
    rhsAxiomClosed gensub-assoc = arvarF _ zero [ arvarF _ one [ arvarF _ two ]1 ]1

{-
    -- AxiomColdTmsub would be empty
    -- AxiomColdCat would be empty

  -- The hot translation
  module _ (cmatfnd : CmatFoundation) where

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
-}
