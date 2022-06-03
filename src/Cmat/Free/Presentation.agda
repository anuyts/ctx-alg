{-# OPTIONS --cubical --type-in-type #-}

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
import Mat.Free.Term
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
      compsub : ∀ {m} {Γ Δ Θ : F.Ctx m} → OperationCold (Γ ⊩ sub Θ)
      mixWhiskerL : ∀ {n p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → OperationCold (Θ F.:⦊ Φ ⊩ sub (Θ F.:⦊ Ψ))
      mixWhiskerR : ∀ {n p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → OperationCold (Γ F.:⦊ Ξ ⊩ sub (Δ F.:⦊ Ξ))
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
    arityCold (compsub {m} {Γ} {Δ} {Θ}) = (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
    arityCold (mixWhiskerL {n} {p} Θ {Φ} {Ψ}) = (Θ ⊩ jhom Φ Ψ) ∷ []
    arityCold (mixWhiskerR {n} {p} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ) ∷ []

    fmatCold : FreeMat (matsigClosed cmatfnd)
    FreeMat.Operation fmatCold = OperationCold
    FreeMat.isSetOperation fmatCold = isSetOperationCold
    FreeMat.arity fmatCold = arityCold

    open MatEqTheory
    open Mat.Free.Term fmatCold

    -- AxiomColdSubst would be empty

    data AxiomColdCat : Jud cmatfnd → Type where
      sub-lUnit : ∀ {m} {Γ Δ : F.Ctx m} → AxiomColdCat (Γ ⊩ sub Δ)
      sub-rUnit : ∀ {m} {Γ Δ : F.Ctx m} → AxiomColdCat (Γ ⊩ sub Δ)
      sub-assoc : ∀ {m} {Γ Δ Θ Λ : F.Ctx m} → AxiomColdCat (Γ ⊩ sub Λ)

    arityAxiomColdCat : ∀{J} → AxiomColdCat J → Arity
    arityAxiomColdCat (sub-lUnit {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomColdCat (sub-rUnit {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomColdCat (sub-assoc {m}{Γ}{Δ}{Θ}{Λ}) = (Θ ⊩ sub Λ) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []

    lhsAxiomColdCat rhsAxiomColdCat : ∀ {J} → (axiom : AxiomColdCat J)
      → TermF (mtyp (arity2mset (arityAxiomColdCat axiom))) J
    lhsAxiomColdCat sub-lUnit = compsub $1 (idsub $1 []) ∷ arvarF zero ∷ []
    lhsAxiomColdCat sub-rUnit = compsub $1 arvarF zero ∷ (idsub $1 []) ∷ []
    lhsAxiomColdCat sub-assoc = compsub $1 (compsub $1 arvarF zero ∷ arvarF one ∷ []) ∷ arvarF two ∷ []
    rhsAxiomColdCat sub-lUnit = arvarF zero
    rhsAxiomColdCat sub-rUnit = arvarF zero
    rhsAxiomColdCat sub-assoc = compsub $1 arvarF zero ∷ (compsub $1 arvarF one ∷ arvarF two ∷ []) ∷ []

    eqTheoryColdCat : MatEqTheory fmatCold
    Axiom eqTheoryColdCat = AxiomColdCat
    msetArity eqTheoryColdCat = arity2mset ∘ arityAxiomColdCat
    lhs eqTheoryColdCat = lhsAxiomColdCat
    rhs eqTheoryColdCat = rhsAxiomColdCat

    matColdCat : Mat (matsigClosed cmatfnd)
    Mat.getFreeMat matColdCat = fmatCold
    Mat.getMatEqTheory matColdCat = eqTheoryColdCat

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

    open MatEqTheory
    open Mat.Free.Term fmatHot

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
      [ cold (mixWhiskerR _) $1 arvarF zero ∷ [] ]1
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
               cold (mixWhiskerR _) $1 arvarF zero ∷ []
             ]1
           )

    data AxiomHotCat : Jud cmatfnd → Type where
      axiomHotTmsub : ∀{J} → (axiom : AxiomHotTmsub J) → AxiomHotCat J
      axiomColdCat : ∀{J} → (axiom : AxiomColdCat cmatfnd J) → AxiomHotCat J
      tmsub-id : ∀ {Γ : F.Ctx m} {rhs : F.RHS m} → AxiomHotCat (Γ ⊩ rhs)
      tmsub-comp : ∀ {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} → AxiomHotCat (Γ ⊩ rhs)

    arityAxiomHotCat : ∀{J} → AxiomHotCat J → Arity
    arityAxiomHotCat (axiomHotTmsub axiom) = arityAxiomHotTmsub axiom
    arityAxiomHotCat (axiomColdCat axiom) = arityAxiomColdCat cmatfnd axiom
    arityAxiomHotCat (tmsub-id {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomHotCat (tmsub-comp {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []

    lhsAxiomHotCat rhsAxiomHotCat : ∀ {J} → (axiom : AxiomHotCat J)
      → TermF (mtyp (arity2mset (arityAxiomHotCat axiom))) J
    lhsAxiomHotCat (axiomHotTmsub axiom) = lhsAxiomHotTmsub axiom
    lhsAxiomHotCat (axiomColdCat axiom) = {!lhsAxiomColdCat cmatfnd axiom!}
    lhsAxiomHotCat tmsub-id = arvarF zero [ cold idsub $1 [] ]1
    lhsAxiomHotCat tmsub-comp = arvarF zero [ cold compsub $1 arvarF one ∷ arvarF two ∷ [] ]1
    rhsAxiomHotCat (axiomHotTmsub axiom) = rhsAxiomHotTmsub axiom
    rhsAxiomHotCat (axiomColdCat axiom) = {!!}
    rhsAxiomHotCat tmsub-id = arvarF zero
    rhsAxiomHotCat tmsub-comp = arvarF zero [ arvarF one ]1 [ arvarF two ]1

{-

    arityAxiomHot : ∀ {J} → AxiomHot J → Arity
    arityAxiomHot (tmsub-id {m} {Γ} {rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomHot (tmsub-comp {m} {Γ} {Δ} {Θ} {rhs}) = (Θ ⊩ rhs) ∷ (◇ ⊩ jhom Δ Θ) ∷ (◇ ⊩ jhom Γ Δ) ∷ []
    arityAxiomHot (tmsub-commut {m} {Γ} {Δ} {rhs} o) = (◇ ⊩ jhom Γ Δ) ∷ translateArityOpen Δ (arity o)

    open Category catModeJunctor renaming (_∘_ to _⊚_)

    lhsHot rhsHot : ∀ {J} → (axiom : AxiomHot J) → TermF (mtyp (arity2mset (arityAxiomHot axiom))) J
    lhsHot tmsub-id = arvarF zero [ inctx id-jhom $1 [] ]1
    lhsHot tmsub-comp = arvarF zero [ arvarF one ]1 [ arvarF two ]1
    lhsHot (tmsub-commut o) = (inctx o $1 tabulateOverLookup (arityHot (inctx o)) (arvarF ∘ suc)) [ arvarF zero ]1
    rhsHot tmsub-id = arvarF zero
    rhsHot tmsub-comp = arvarF zero [ inctx comp-jhom $1
      subst (TermF _) (cong (_⊩ _) (sym (⋆IdR ◇))) (arvarF two) ∷
      subst (TermF _) (cong (_⊩ _) (sym (⋆IdR ◇))) (arvarF one)
      ∷ [] ]1
    rhsHot (tmsub-commut {m} {Γ} {Δ} {rhs} o) = inctx o $1 tabulateOverLookup (arityHot (inctx o)) (λ pΓ → (
        let {- Because the action of map is not definitional,
               everything comes in 3 flavours: the original one, the one in ctx Γ, and the one in ctx Δ.
            -}
            p : Fin (length (arity o))
            p = subst Fin (length-translateArityOpen Γ (arity o)) pΓ
            pΔ : Fin (length (translateArityOpen Δ (arity o)))
            pΔ = subst⁻ Fin (length-translateArityOpen Δ (arity o)) p
            pΓ-eq : PathP (λ i → Fin (length-translateArityOpen Γ (arity o) i)) pΓ p
            pΓ-eq = subst-filler Fin (length-translateArityOpen Γ (arity o)) pΓ
            pΔ-eq : PathP (λ i → Fin (length-translateArityOpen Δ (arity o) i)) pΔ p
            pΔ-eq = symP (subst⁻-filler Fin (length-translateArityOpen Δ (arity o)) p)
            Jₚ = lookup (arity o) p
            mₚ = jud'mode Jₚ
            Φₚ = jud'ctx Jₚ
            rhsₚ = jud'rhs Jₚ
            JₚΓ = lookup (translateArityOpen Γ (arity o)) pΓ
            mₚΓ = jud'mode JₚΓ
            Γ⦊Φₚ = jud'ctx JₚΓ
            rhsₚΓ = jud'rhs JₚΓ
            JₚΔ = lookup (translateArityOpen Δ (arity o)) pΔ
            mₚΔ = jud'mode JₚΔ
            Δ⦊Φₚ = jud'ctx JₚΔ
            rhsₚΔ = jud'rhs JₚΔ
            JₚΓ-eq : JₚΓ ≡ _
            JₚΓ-eq = lookup-translateArityOpen Γ (arity o) pΓ p pΓ-eq
            mₚΓ-eq : mₚΓ ≡ mₚ
            mₚΓ-eq = cong jud'mode JₚΓ-eq
            Γ⦊Φₚ-eq : PathP (λ i → Junctor m0 (mₚΓ-eq i)) (Γ⦊Φₚ) (Γ ⦊ Φₚ)
            Γ⦊Φₚ-eq = cong jud'ctx JₚΓ-eq
            rhsₚΓ-eq : PathP (λ i → RHS (mₚΓ-eq i)) rhsₚΓ rhsₚ
            rhsₚΓ-eq = cong jud'rhs JₚΓ-eq
            JₚΔ-eq : JₚΔ ≡ _
            JₚΔ-eq = lookup-translateArityOpen Δ (arity o) pΔ p pΔ-eq
            mₚΔ-eq : mₚΔ ≡ mₚ
            mₚΔ-eq = cong jud'mode JₚΔ-eq
            Δ⦊Φₚ-eq : PathP (λ i → Junctor m0 (mₚΔ-eq i)) (Δ⦊Φₚ) (Δ ⦊ Φₚ)
            Δ⦊Φₚ-eq = cong jud'ctx JₚΔ-eq
            rhsₚΔ-eq : PathP (λ i → RHS (mₚΔ-eq i)) rhsₚΔ rhsₚ
            rhsₚΔ-eq = cong jud'rhs JₚΔ-eq
        in -- Need a term of type Γ⦊Φₚ ⊩ rhsₚΓ @ mₚΓ
           subst (TermF _) (sym JₚΓ-eq) (
             -- Need a term of type Γ ⦊ Φₚ ⊩ rhsₚ @ mₚ
             ( -- Need a term of type Δ ⦊ Φₚ ⊩ rhsₚ @ mₚ
               subst (TermF _) JₚΔ-eq (
                 -- Need a term of type Δ⦊Φₚ ⊩ rhsₚΔ @ mₚΔ
                 arvarF (suc pΔ)
               )
             )
             [
               inctx (whiskerR Φₚ) $1 (
                 subst (TermF _) (cong (_⊩ jhom Γ Δ) (sym (⋆IdR ◇))) (arvarF zero)
               ) ∷ []
             ]1
           )
      ))

    eqTheoryHot : MatEqTheory fmatHot
    Axiom eqTheoryHot = AxiomHot
    --isSetAxiom eqTheoryHot = isSetAxiomHot
    msetArity eqTheoryHot = arity2mset ∘ arityAxiomHot
    lhs eqTheoryHot = lhsHot
    rhs eqTheoryHot = rhsHot

    matHot : Mat (matsigOpen m0)
    Mat.getFreeMat matHot = fmatHot
    Mat.getMatEqTheory matHot = eqTheoryHot
-}
