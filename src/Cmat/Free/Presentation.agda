{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Cubical.Data.List.FinData
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
        → OperationCold (translateJudClosed cmatfnd Γ (◇ ⊩ rhs))
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
    arityCold (mixWhiskerR {n} {p} {Ω} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ) ∷ (Ω ⊩ sub (Γ F.:⦊ Ξ)) ∷ []

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

    data AxiomHotTmsub : Jud cmatfnd → Type where
      tmsub-commut : ∀ {m} {Γ Δ : F.Ctx m} {rhs : LoneRHS m} (o : Operation rhs)
        → AxiomHotTmsub (translateJudClosed cmatfnd Γ (◇ ⊩ rhs))

    arityAxiomHotTmsub : ∀{J} → AxiomHotTmsub J → Arity
    arityAxiomHotTmsub (tmsub-commut {m} {Γ} {Δ} {rhs} o) = (Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o)

    lhsAxiomHotTmsub rhsAxiomHotTmsub : ∀ {J} → (axiom : AxiomHotTmsub J)
      → TermF (mtyp (arity2mset (arityAxiomHotTmsub axiom))) J
    lhsAxiomHotTmsub (tmsub-commut {m} {Γ} {Δ} {rhs} o) =
      (cold (inctx o) $1 tabulateOverLookup (arityCold cmatfnd (inctx o)) (arvarF ∘ suc))
      [ cold (mixWhiskerR _) $1 arvarF zero ∷ (cold idsub $1 []) ∷ [] ]1
    rhsAxiomHotTmsub (tmsub-commut {m} {Γ} {Δ} {rhs} o) =
      cold (inctx o) $1 tabulateOverLookup (arityCold cmatfnd (inctx o)) λ pΓ →
        let p : Fin (length (arity o))
            p = subst Fin (length-translateArityClosed cmatfnd Γ (arity o)) pΓ
            pΔ : Fin (length (translateArityClosed cmatfnd Δ (arity o)))
            pΔ = subst⁻ Fin (length-translateArityClosed cmatfnd Δ (arity o)) p
            pΓ-eq : PathP (λ i → Fin (length-translateArityClosed cmatfnd Γ (arity o) i)) pΓ p
            pΓ-eq = subst-filler Fin (length-translateArityClosed cmatfnd Γ (arity o)) pΓ
            pΔ-eq : PathP (λ i → Fin (length-translateArityClosed cmatfnd Δ (arity o) i)) pΔ p
            pΔ-eq = symP (subst⁻-filler Fin (length-translateArityClosed cmatfnd Δ (arity o)) p)
            Jₚ = lookup (arity o) p
            JₚΓ = lookup (translateArityClosed cmatfnd Γ (arity o)) pΓ
            JₚΓ-eq : JₚΓ ≡ _
            JₚΓ-eq = lookup-translateArityClosed cmatfnd Γ (arity o) pΓ p pΓ-eq
            JₚΔ = lookup (translateArityClosed cmatfnd Δ (arity o)) pΔ
            JₚΔ-eq : JₚΔ ≡ _
            JₚΔ-eq = lookup-translateArityClosed cmatfnd Δ (arity o) pΔ p pΔ-eq
        in -- need a term at JₚΓ
           subst (TermF _) (sym JₚΓ-eq) (
             -- need a term at translateJudClosed cmatfnd Γ Jₚ
             ( -- need a term at translateJudClosed cmatfnd Δ Jₚ
               subst (TermF _) JₚΔ-eq (
                 -- need a term at JₚΔ
                 arvarF (suc pΔ)
               )
             )
             [
               cold (mixWhiskerR _) $1 arvarF zero ∷ (cold idsub $1 []) ∷ []
             ]1
           )

    eqTheoryHotTmsub : MatEqTheory fmatHot
    Axiom eqTheoryHotTmsub = AxiomHotTmsub
    msetArity eqTheoryHotTmsub = arity2mset ∘ arityAxiomHotTmsub
    lhs eqTheoryHotTmsub = lhsAxiomHotTmsub
    rhs eqTheoryHotTmsub = rhsAxiomHotTmsub

    matHotTmsub : Mat (matsigClosed cmatfnd)
    Mat.getFreeMat matHotTmsub = fmatHot
    Mat.getMatEqTheory matHotTmsub = eqTheoryHotTmsub

    data AxiomHotCat : Jud cmatfnd → Type where
      axiomHotTmsub : ∀{J} → (axiom : AxiomHotTmsub J) → AxiomHotCat J
      --axiomColdCat : ∀{J} → (axiom : AxiomColdCat cmatfnd J) → AxiomHotCat J
      tmsub-lunit : ∀ {Γ Δ : F.Ctx m} → AxiomHotCat (Γ ⊩ sub Δ)
      tmsub-runit : ∀ {Γ : F.Ctx m} {rhs : F.RHS m} → AxiomHotCat (Γ ⊩ rhs)
      tmsub-assoc : ∀ {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} → AxiomHotCat (Γ ⊩ rhs)

    arityAxiomHotCat : ∀{J} → AxiomHotCat J → Arity
    arityAxiomHotCat (axiomHotTmsub axiom) = arityAxiomHotTmsub axiom
    --arityAxiomHotCat (axiomColdCat axiom) = arityAxiomColdCat cmatfnd axiom
    arityAxiomHotCat (tmsub-lunit {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomHotCat (tmsub-runit {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomHotCat (tmsub-assoc {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []

    lhsAxiomHotCat rhsAxiomHotCat : ∀ {J} → (axiom : AxiomHotCat J)
      → TermF (mtyp (arity2mset (arityAxiomHotCat axiom))) J
    lhsAxiomHotCat (axiomHotTmsub axiom) = lhsAxiomHotTmsub axiom
    --lhsAxiomHotCat (axiomColdCat axiom) = opmapTermF _ _ ophomCold→Hot _ (lhsAxiomColdCat cmatfnd axiom)
    lhsAxiomHotCat tmsub-lunit = (cold idsub $1 []) [ arvarF zero ]1
    lhsAxiomHotCat tmsub-runit = arvarF zero [ cold idsub $1 [] ]1
    lhsAxiomHotCat tmsub-assoc = arvarF zero [ arvarF one ]1 [ arvarF two ]1
    rhsAxiomHotCat (axiomHotTmsub axiom) = rhsAxiomHotTmsub axiom
    --rhsAxiomHotCat (axiomColdCat axiom) = opmapTermF _ _ ophomCold→Hot _ (rhsAxiomColdCat cmatfnd axiom)
    rhsAxiomHotCat tmsub-lunit = arvarF zero
    rhsAxiomHotCat tmsub-runit = arvarF zero
    rhsAxiomHotCat tmsub-assoc = arvarF zero [ arvarF one [ arvarF two ]1 ]1

    eqTheoryHotCat : MatEqTheory fmatHot
    Axiom eqTheoryHotCat = AxiomHotCat
    msetArity eqTheoryHotCat = arity2mset ∘ arityAxiomHotCat
    lhs eqTheoryHotCat = lhsAxiomHotCat
    rhs eqTheoryHotCat = rhsAxiomHotCat

    matHotCat : Mat (matsigClosed cmatfnd)
    Mat.getFreeMat matHotCat = fmatHot
    Mat.getMatEqTheory matHotCat = eqTheoryHotCat
