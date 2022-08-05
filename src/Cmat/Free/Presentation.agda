{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
import Cubical.Foundations.Id as Id
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

    data OperationClosed : (temp : Temp) → Jud cmatfnd → Type where
      inctx : ∀ {temp} {m} {Γ : F.Ctx m} {rhs : LoneRHS m} → (o : Operation rhs)
        → OperationClosed temp (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
        -- → OperationClosed temp (translateJudClosed cmatfnd Γ (◇ ⊩ rhs))
      idsub : ∀ {temp} {m} {Γ : F.Ctx m} → OperationClosed temp (Γ ⊩ sub Γ)
      --compsub : ∀ {m} {Γ Δ Θ : F.Ctx m} → OperationClosed temp (Γ ⊩ sub Θ)
      -- The following two involve a delayed substitution from Ω
      mixWhiskerL : ∀ {temp} {n p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → OperationClosed temp (Θ F.:⦊ Φ ⊩ sub (Θ F.:⦊ Ψ))
      mixWhiskerR : ∀ {temp} {n p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → OperationClosed temp (Γ F.:⦊ Ξ ⊩ sub (Δ F.:⦊ Ξ))
      -- mixWhiskerL t ∘ mixWhiskerR s = mixWhiskerR s ∘ mixWhiskerL (t [ Γ.s ])
      -- mixWhiskerL (whiskerR t) = mixWhiskerR (mixWhiskerL t)
      -- mixWhiskerL respects id-jhom and comp-jhom
      -- mixWhiskerR respects idsub and compsub
      -- mixWhiskerL respects :⦊
      -- mixWhiskerR respects ◇ and ⦊
      gensub : ∀ {temp} {m} {Γ Δ : F.Ctx m} {rhs : F.RHS m}
        → {{u : F.Substitutable temp rhs}} → OperationClosed temp (Γ ⊩ rhs)

    pattern tmsub = gensub {hot} {{tt}}
    pattern compsub = gensub {cold} {{tt}}

    OperationCold = OperationClosed cold
    OperationHot = OperationClosed hot

    isSetOperationClosed : ∀ {temp} {J} → isSet (OperationClosed temp J)
    isSetOperationClosed = {!!} -- via reflection

    arityClosed : ∀ {temp} {J} → OperationClosed temp J → Arity
    arityClosed (inctx {temp} {m} {Γ} {rhs} o) = translateArityClosed cmatfnd Γ (arity o)
    arityClosed idsub = []
    arityClosed (mixWhiskerL {temp} {n} {p} Θ {Φ} {Ψ}) = (Θ ⊩ jhom Φ Ψ) ∷ []
    arityClosed (mixWhiskerR {temp} {n} {p} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ)    ∷ []
    arityClosed (gensub {temp} {m} {Γ} {Δ} {rhs}) = (Δ ⊩ rhs) ∷ (Γ ⊩ sub Δ) ∷ []

    fmatClosed : Temp → FreeMat (matsigClosed cmatfnd)
    FreeMat.Operation (fmatClosed temp) = OperationClosed temp
    FreeMat.isSetOperation (fmatClosed temp) = isSetOperationClosed
    FreeMat.arity (fmatClosed temp) = arityClosed

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
      module TermFClosed (temp : Temp) = TermF (fmatClosed temp)
    open TermFClosed

    pattern _[_]1 t σ = gensub $1 (t ∷ σ ∷ [])
    infixl 7 _[_]1

    data AxiomClosed : Temp → Jud cmatfnd → Type where
      -- The output of tmsub-inctx has a translated rhs, which is never a sub.
      -- Therefore, for it to be substitutable, we need to be in the hot case.
      tmsub-inctx : ∀ {m} {Γ Δ : F.Ctx m} {rhs : LoneRHS m} (o : Operation rhs)
        → AxiomClosed hot (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
      gensub-lunit : ∀ {temp} {Γ Δ : F.Ctx m} → AxiomClosed temp (Γ ⊩ sub Δ)
      gensub-runit : ∀ {temp} {Γ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable temp rhs}} → AxiomClosed temp (Γ ⊩ rhs)
      gensub-assoc : ∀ {temp} {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable temp rhs}} → AxiomClosed temp (Γ ⊩ rhs)

    AxiomCold = AxiomClosed cold
    AxiomHot = AxiomClosed hot

    arityAxiomClosed : ∀ {temp} {J} → AxiomClosed temp J → Arity
    arityAxiomClosed (tmsub-inctx {m} {Γ} {Δ} {rhs} o) = (Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o)
    arityAxiomClosed (gensub-lunit {temp} {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomClosed (gensub-runit {temp} {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomClosed (gensub-assoc {temp} {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []

    lhsAxiomClosed rhsAxiomClosed : ∀ {temp} {J} → (axiom : AxiomClosed temp J)
      → TermF temp (mtyp (arity2mset (arityAxiomClosed axiom))) J
    lhsAxiomClosed (tmsub-inctx {m} {Γ} {Δ} {rhs} o) =
      (inctx o $1 tabulateOverLookup (arityClosed {hot} (inctx o)) (arvarF _ ∘ suc)) [ arvarF _ zero ]1
    lhsAxiomClosed gensub-lunit = (idsub $1 []) [ arvarF _ zero ]1
    lhsAxiomClosed gensub-runit = arvarF _ zero [ idsub $1 [] ]1
    lhsAxiomClosed gensub-assoc = arvarF _ zero [ arvarF _ one ]1 [ arvarF _ two ]1
    rhsAxiomClosed (tmsub-inctx {m} {Γ} {Δ} {rhs} o) =
      inctx o $1 mapOverSpan
        {B = TermF hot (mtyp (arity2mset ((Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o))))}
        {B' = TermF hot (mtyp (arity2mset (arityAxiomClosed {hot} (tmsub-inctx o))))}
        (translateJudClosed cmatfnd Δ)
        (translateJudClosed cmatfnd Γ)
        (λ J x → x [ mixWhiskerR _ $1 arvarF _ zero ∷ [] ]1)
        (arity o)
        (tabulateOverLookup (arityClosed {hot} (inctx o)) (arvarF _ ∘ suc))
    rhsAxiomClosed gensub-lunit = arvarF _ zero
    rhsAxiomClosed gensub-runit = arvarF _ zero
    rhsAxiomClosed gensub-assoc = arvarF _ zero [ arvarF _ one [ arvarF _ two ]1 ]1

    eqTheoryClosed : (temp : Temp) → MatEqTheory (fmatClosed temp)
    Axiom (eqTheoryClosed temp) = AxiomClosed temp
    msetArity (eqTheoryClosed temp) = arity2mset ∘ arityAxiomClosed
    lhs (eqTheoryClosed temp) = lhsAxiomClosed
    rhs (eqTheoryClosed temp) = rhsAxiomClosed

    eqTheoryCold = eqTheoryClosed cold
    eqTheoryHot = eqTheoryClosed hot

    matClosed : Temp → Mat (matsigClosed cmatfnd)
    Mat.getFreeMat (matClosed temp) = fmatClosed temp
    Mat.getMatEqTheory (matClosed temp) = eqTheoryClosed temp

    matCold = matClosed cold
    matHot = matClosed hot
