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

open Category hiding (_∘_)

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
    idJHom : ∀ {m n} {Φ : Junctor m n} → Operation (jhom Φ Φ)
    compJHom : ∀ {m n} {Φ Ψ Ξ : Junctor m n} → Operation (jhom Φ Ξ)
    whiskerL : ∀ {m n p} (Ξ : Junctor m n) {Φ Ψ : Junctor n p} → Operation (jhom (Ξ ⦊ Φ) (Ξ ⦊ Ψ))
    whiskerR : ∀ {m n p} {Φ Ψ : Junctor m n} (Ξ : Junctor n p) → Operation (jhom (Φ ⦊ Ξ) (Ψ ⦊ Ξ))
    -- whiskerL t ∘ whiskerR s = whiskerR s ∘ whiskerL (t [ Γ.s ])
    -- whiskerL (whiskerR t) = whiskerR (whiskerL t)
    -- whiskerL respects idJHom and compJHom
    -- whiskerR respects idJHom and compJHom
    -- whiskerL respects ◇ and ⦊
    -- whiskerR respects ◇ and ⦊

  isSetOperation : ∀ {m} {rhs : LoneRHS m} → isSet (Operation rhs)
  isSetOperation = {!!} -- via reflection

  arity : ∀ {m} {rhs : LoneRHS m} → Operation rhs → CArity m
  arity (custom o) = arityCustom o
  arity idJHom = []
  arity (compJHom {m} {n} {Φ} {Ψ} {Ξ}) = (◇ ⊩ jhom Ψ Ξ) ∷ (◇ ⊩ jhom Φ Ψ) ∷ []
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
      mixWhiskerL : ∀ {temp} {n p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → OperationClosed temp (Θ F.:⦊ Φ ⊩ sub (Θ F.:⦊ Ψ))
      mixWhiskerR : ∀ {temp} {n p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → OperationClosed temp (Γ F.:⦊ Ξ ⊩ sub (Δ F.:⦊ Ξ))
      gensub : ∀ {temp} {m} {Γ Δ : F.Ctx m} {rhs : F.RHS m}
        → {{u : F.Substitutable temp rhs}} → OperationClosed temp (Γ ⊩ rhs)

    pattern tmsub = gensub {hot} {{tt}}
    pattern compsub = gensub {rhs = sub _}

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

    substCtxRHS⁻ : ∀ {heat} {m} {X} {Γ Γ' : F.Ctx m} {rhs rhs'}
      → Γ ≡ Γ'
      → rhs ≡ rhs'
      → TermF heat X (Γ' ⊩ rhs')
      → TermF heat X (Γ ⊩ rhs)
    substCtxRHS⁻ {heat} {m} {X} pΓ prhs t = subst⁻ (TermF heat X) (cong₂ _⊩_ pΓ prhs) t

    substCtx⁻ : ∀ {heat} {m} {X} {Γ Γ' : F.Ctx m} {rhs}
      → Γ ≡ Γ'
      → TermF heat X (Γ' ⊩ rhs)
      → TermF heat X (Γ ⊩ rhs)
    substCtx⁻ pΓ = substCtxRHS⁻ pΓ refl

    substRHS⁻ : ∀ {heat} {m} {X} {Γ : F.Ctx m} {rhs rhs'}
      → rhs ≡ rhs'
      → TermF heat X (Γ ⊩ rhs')
      → TermF heat X (Γ ⊩ rhs)
    substRHS⁻ = substCtxRHS⁻ refl

    pattern _[_]1 t σ = gensub $1 (t ∷ σ ∷ [])
    infixl 7 _[_]1

    data AxiomClosed : Temp → Jud cmatfnd → Type where
      -- The output of tmsub-inctx has a translated rhs, which is never a sub.
      -- Therefore, for it to be substitutable, we need to be in the hot case.
      gensub-inctx : ∀ {m} {Γ Δ : F.Ctx m} {rhs : LoneRHS m} (o : Operation rhs)
        → AxiomClosed hot (Γ ⊩ translateRHSClosedEmptyContext cmatfnd rhs)
      gensub-lunit : ∀ {temp} {Γ Δ : F.Ctx m} → AxiomClosed temp (Γ ⊩ sub Δ)
      gensub-runit : ∀ {temp} {Γ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable temp rhs}} → AxiomClosed temp (Γ ⊩ rhs)
      gensub-assoc : ∀ {temp} {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable temp rhs}} → AxiomClosed temp (Γ ⊩ rhs)
      -- mixWhiskerL t ∘ mixWhiskerR s = mixWhiskerR s ∘ mixWhiskerL (t [ Γ.s ])
      -- We cannot yet state this, because we cannot substitute t in the cold model.
      -- This will be added together with the custom rules that can also refer to substitution.
      --gensub-mixWhiskerLR : ∀ {temp} {Γ Δ : F.Ctx m} {Φ Ψ : Junctor m n} → AxiomClosed temp (Γ F.:⦊ Φ ⊩ sub (Δ F.:⦊ Ψ))
      -- mixWhiskerL (whiskerR t) = mixWhiskerR (mixWhiskerL t)
      mixWhiskerL-whiskerR : ∀ {temp} {m n o : Mode} {Γ : F.Ctx m} {Φ Ψ : Junctor m n} {Ξ : Junctor n o}
        → AxiomClosed temp (Γ F.:⦊ (Φ ⦊ Ξ) ⊩ sub (Γ F.:⦊ (Ψ ⦊ Ξ)))
      -- mixWhiskerL respects idJHom and compJHom
      mixWhiskerL-idJHom : ∀ {temp} {m n : Mode} {Γ : F.Ctx m} {Φ : Junctor m n}
        → AxiomClosed temp ((Γ F.:⦊ Φ) ⊩ sub (Γ F.:⦊ Φ))
      mixWhiskerL-compJHom : ∀ {temp} {m n : Mode} {Γ : F.Ctx m} {Φ Ψ Ξ : Junctor m n}
        → AxiomClosed temp ((Γ F.:⦊ Φ) ⊩ sub (Γ F.:⦊ Ξ))
      -- mixWhiskerR respects idsub and compsub
      mixWhiskerR-idsub : ∀ {temp} {m n : Mode} {Γ : F.Ctx m} {Φ : Junctor m n}
        → AxiomClosed temp ((Γ F.:⦊ Φ) ⊩ sub (Γ F.:⦊ Φ))
      mixWhiskerR-compsub : ∀ {temp} {m n : Mode} {Γ Δ Θ : F.Ctx m} {Φ : Junctor m n}
        → AxiomClosed temp ((Γ F.:⦊ Φ) ⊩ sub (Θ F.:⦊ Φ))
      -- mixWhiskerL respects :⦊
      mixWhiskerL-:⦊ : ∀ {temp} {m n o : Mode} {Γ : F.Ctx m} {Φ : Junctor m n} {Ψ Ξ : Junctor n o}
        → AxiomClosed temp ((Γ F.:⦊ Φ) F.:⦊ Ψ ⊩ sub ((Γ F.:⦊ Φ) F.:⦊ Ξ))
      -- mixWhiskerR respects ◇ and ⦊
      mixWhiskerR-◇ : ∀ {temp} {m : Mode} {Γ Δ : F.Ctx m}
        → AxiomClosed temp (Γ F.:⦊ ◇ ⊩ sub (Δ F.:⦊ ◇))
      mixWhiskerR-⦊ : ∀ {temp} {m n o : Mode} {Γ Δ : F.Ctx m} {Φ : Junctor m n} {Ψ : Junctor n o}
        → AxiomClosed temp (Γ F.:⦊ (Φ ⦊ Ψ) ⊩ sub (Δ F.:⦊ (Φ ⦊ Ψ)))

    AxiomCold = AxiomClosed cold
    AxiomHot = AxiomClosed hot

    arityAxiomClosed : ∀ {temp} {J} → AxiomClosed temp J → Arity
    arityAxiomClosed (gensub-inctx {m} {Γ} {Δ} {rhs} o) = (Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o)
    arityAxiomClosed (gensub-lunit {temp} {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomClosed (gensub-runit {temp} {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomClosed (gensub-assoc {temp} {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
    --arityAxiomClosed (gensub-mixWhiskerLR {temp} {m}{n} {Γ}{Δ}{Φ}{Ψ}) = (Δ ⊩ jhom Φ Ψ) ∷ (Γ ⊩ sub Δ) ∷ []
    arityAxiomClosed (mixWhiskerL-whiskerR {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) = (Γ ⊩ jhom Φ Ψ) ∷ []
    arityAxiomClosed (mixWhiskerL-idJHom {temp} {m}{n} {Γ}{Φ}) = []
    arityAxiomClosed (mixWhiskerL-compJHom {temp} {m}{n} {Γ}{Φ}{Ψ}{Ξ}) = (Γ ⊩ jhom Ψ Ξ) ∷ (Γ ⊩ jhom Φ Ψ) ∷ []
    arityAxiomClosed (mixWhiskerR-idsub {temp} {m}{n} {Γ}{Φ}) = []
    arityAxiomClosed (mixWhiskerR-compsub {temp} {m}{n} {Γ}{Δ}{Θ}{Φ}) = (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
    arityAxiomClosed (mixWhiskerL-:⦊ {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) = (Γ F.:⦊ Φ ⊩ jhom Ψ Ξ) ∷ []
    arityAxiomClosed (mixWhiskerR-◇ {temp} {m} {Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomClosed (mixWhiskerR-⦊ {temp} {m}{n}{o} {Γ}{Δ}{Φ}{Ψ}) = (Γ ⊩ sub Δ) ∷ []

    lhsAxiomClosed rhsAxiomClosed : ∀ {temp} {J} → (axiom : AxiomClosed temp J)
      → TermF temp (mtyp (arity2mset (arityAxiomClosed axiom))) J
    lhsAxiomClosed (gensub-inctx {m} {Γ} {Δ} {rhs} o) =
      (inctx o $1 tabulateOverLookup (arityClosed {hot} (inctx o)) (arvarF _ ∘ suc)) [ arvarF _ zero ]1
    lhsAxiomClosed gensub-lunit = (idsub $1 []) [ arvarF _ zero ]1
    lhsAxiomClosed gensub-runit = arvarF _ zero [ idsub $1 [] ]1
    lhsAxiomClosed gensub-assoc = arvarF _ zero [ arvarF _ one ]1 [ arvarF _ two ]1
    --lhsAxiomClosed (gensub-mixWhiskerLR {temp} {m}{n} {Γ}{Δ}{Φ}{Ψ}) =
    --  (mixWhiskerL Δ $1 arvarF _ zero ∷ []) [ mixWhiskerR Φ $1 arvarF _ one ∷ [] ]1
    lhsAxiomClosed (mixWhiskerL-whiskerR {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      mixWhiskerL Γ $1 (inctx (whiskerR Ξ) $1 substCtx⁻ (F.:⦊IdR Γ) (arvarF _ zero) ∷ []) ∷ []
    lhsAxiomClosed (mixWhiskerL-idJHom {temp} {m}{n} {Γ}{Φ}) =
      mixWhiskerL Γ $1 (inctx idJHom $1 []) ∷ []
    lhsAxiomClosed (mixWhiskerL-compJHom {temp} {m}{n} {Γ}{Φ}{Ψ}{Ξ}) =
      mixWhiskerL Γ $1 (inctx compJHom $1
        substCtx⁻ (F.:⦊IdR Γ) (arvarF _ zero) ∷
        substCtx⁻ (F.:⦊IdR Γ) (arvarF _ one) ∷ []) ∷ []
    lhsAxiomClosed (mixWhiskerR-idsub {temp} {m}{n} {Γ}{Φ}) =
      mixWhiskerR Φ $1 (idsub $1 []) ∷ []
    lhsAxiomClosed (mixWhiskerR-compsub {temp} {m}{n} {Γ}{Δ}{Θ}{Φ}) =
      mixWhiskerR Φ $1 (compsub $1 arvarF _ zero ∷ arvarF _ one ∷ []) ∷ []
    lhsAxiomClosed (mixWhiskerL-:⦊ {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      mixWhiskerL (Γ F.:⦊ Φ) $1 arvarF _ zero ∷ []
    lhsAxiomClosed (mixWhiskerR-◇ {temp} {m} {Γ}{Δ}) =
      mixWhiskerR ◇ $1 arvarF _ zero ∷ []
    lhsAxiomClosed (mixWhiskerR-⦊ {temp} {m}{n}{o} {Γ}{Δ}{Φ}{Ψ}) =
      mixWhiskerR (Φ ⦊ Ψ) $1 arvarF _ zero ∷ []

    rhsAxiomClosed (gensub-inctx {m} {Γ} {Δ} {rhs} o) =
      inctx o $1 mapOverSpan
        {B = TermF hot (mtyp (arity2mset ((Γ ⊩ sub Δ) ∷ translateArityClosed cmatfnd Δ (arity o))))}
        {B' = TermF hot (mtyp (arity2mset (arityAxiomClosed {hot} (gensub-inctx o))))}
        (translateJudClosed cmatfnd Δ)
        (translateJudClosed cmatfnd Γ)
        (λ J x → x [ mixWhiskerR _ $1 arvarF _ zero ∷ [] ]1)
        (arity o)
        (tabulateOverLookup (arityClosed {hot} (inctx o)) (arvarF _ ∘ suc))
    rhsAxiomClosed gensub-lunit = arvarF _ zero
    rhsAxiomClosed gensub-runit = arvarF _ zero
    rhsAxiomClosed gensub-assoc = arvarF _ zero [ arvarF _ one [ arvarF _ two ]1 ]1
    --rhsAxiomClosed (gensub-mixWhiskerLR {temp} {m}{n} {Γ}{Δ}{Φ}{Ψ}) =
    --  (mixWhiskerR Ψ $1 arvarF _ one ∷ []) [ mixWhiskerL Γ $1 {!? [ ? ]1!} ∷ [] ]1
    rhsAxiomClosed (mixWhiskerL-whiskerR {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      substCtxRHS⁻ (sym (F.:⦊Assoc Γ Φ Ξ)) (cong sub (sym (F.:⦊Assoc Γ Ψ Ξ))) (
        mixWhiskerR Ξ $1 (mixWhiskerL Γ $1 arvarF _ zero ∷ []) ∷ []
      )
    rhsAxiomClosed (mixWhiskerL-idJHom {temp} {m}{n} {Γ}{Φ}) = idsub $1 []
    rhsAxiomClosed (mixWhiskerL-compJHom {temp} {m}{n} {Γ}{Φ}{Ψ}{Ξ}) = compsub $1
      (mixWhiskerL Γ $1 arvarF _ zero ∷ []) ∷
      (mixWhiskerL Γ $1 arvarF _ one ∷ []) ∷ []
    rhsAxiomClosed (mixWhiskerR-idsub {temp} {m}{n} {Γ}{Φ}) = idsub $1 []
    rhsAxiomClosed (mixWhiskerR-compsub {temp} {m}{n} {Γ}{Δ}{Θ}{Φ}) = compsub $1
      (mixWhiskerR Φ $1 arvarF _ zero ∷ []) ∷
      (mixWhiskerR Φ $1 arvarF _ one ∷ []) ∷ []
    rhsAxiomClosed (mixWhiskerL-:⦊ {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      substCtxRHS⁻ (F.:⦊Assoc Γ Φ Ψ) (cong sub (F.:⦊Assoc Γ Φ Ξ)) (
        mixWhiskerL Γ $1 (inctx (whiskerL Φ) $1 arvarF _ zero ∷ []) ∷ []
      )
    rhsAxiomClosed (mixWhiskerR-◇ {temp} {m} {Γ}{Δ}) =
      substCtxRHS⁻ (F.:⦊IdR Γ) (cong sub (F.:⦊IdR Δ)) (arvarF _ zero)
    rhsAxiomClosed (mixWhiskerR-⦊ {temp} {m}{n}{o} {Γ}{Δ}{Φ}{Ψ}) =
      substCtxRHS⁻ (sym (F.:⦊Assoc Γ Φ Ψ)) (cong sub (sym (F.:⦊Assoc Δ Φ Ψ))) (
        mixWhiskerR Ψ $1 (mixWhiskerR Φ $1 arvarF _ zero ∷ []) ∷ []
      )

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
