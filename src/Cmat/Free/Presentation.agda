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
  LoneRHS m = RHS (cmatfndLevitated m) m

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

    open MatSignature (matsigSettled cmatfnd)
    private
      module F = CmatFoundation cmatfnd

    data OperationSettled : (temp : Temp) → Jud cmatfnd → Type where
      inctx : ∀ {temp} {m} {Γ : F.Ctx m} {rhs : LoneRHS m} → (o : Operation rhs)
        → OperationSettled temp (Γ ⊩ translateRHSSettledEmptyContext cmatfnd rhs)
        -- → OperationSettled temp (translateJudSettled cmatfnd Γ (◇ ⊩ rhs))
      idsub : ∀ {temp} {m} {Γ : F.Ctx m} → OperationSettled temp (Γ ⊩ sub Γ)
      mixWhiskerL : ∀ {temp} {n p} (Θ : F.Ctx n) {Φ Ψ : Junctor n p} → OperationSettled temp (Θ F.:⦊ Φ ⊩ sub (Θ F.:⦊ Ψ))
      mixWhiskerR : ∀ {temp} {n p} {Γ Δ : F.Ctx n} (Ξ : Junctor n p) → OperationSettled temp (Γ F.:⦊ Ξ ⊩ sub (Δ F.:⦊ Ξ))
      gensub : ∀ {temp} {m} {Γ Δ : F.Ctx m} {rhs : F.RHS m}
        → {{u : F.Substitutable temp rhs}} → OperationSettled temp (Γ ⊩ rhs)

    pattern tmsub = gensub {hot} {{tt}}
    pattern compsub = gensub {rhs = sub _}

    OperationCold = OperationSettled cold
    OperationHot = OperationSettled hot

    isSetOperationSettled : ∀ {temp} {J} → isSet (OperationSettled temp J)
    isSetOperationSettled = {!!} -- via reflection

    aritySettled : ∀ {temp} {J} → OperationSettled temp J → Arity
    aritySettled (inctx {temp} {m} {Γ} {rhs} o) = translateAritySettled cmatfnd Γ (arity o)
    aritySettled idsub = []
    aritySettled (mixWhiskerL {temp} {n} {p} Θ {Φ} {Ψ}) = (Θ ⊩ jhom Φ Ψ) ∷ []
    aritySettled (mixWhiskerR {temp} {n} {p} {Γ} {Δ} Ξ) = (Γ ⊩ sub Δ)    ∷ []
    aritySettled (gensub {temp} {m} {Γ} {Δ} {rhs}) = (Δ ⊩ rhs) ∷ (Γ ⊩ sub Δ) ∷ []

    arityCold = aritySettled {cold}
    arityHot = aritySettled {hot}

    fmatSettled : Temp → FreeMat (matsigSettled cmatfnd)
    FreeMat.Operation (fmatSettled temp) = OperationSettled temp
    FreeMat.isSetOperation (fmatSettled temp) = isSetOperationSettled
    FreeMat.arity (fmatSettled temp) = aritySettled

    fmatCold = fmatSettled cold
    fmatHot = fmatSettled hot

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
      module TermFSettled (temp : Temp) = TermF (fmatSettled temp)
    open TermFSettled

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

    data AxiomSettled : Temp → Jud cmatfnd → Type where
      -- The output of tmsub-inctx has a translated rhs, which is never a sub.
      -- Therefore, for it to be substitutable, we need to be in the hot case.
      gensub-inctx : ∀ {m} {Γ Δ : F.Ctx m} {rhs : LoneRHS m} (o : Operation rhs)
        → AxiomSettled hot (Γ ⊩ translateRHSSettledEmptyContext cmatfnd rhs)
      gensub-lunit : ∀ {temp} {Γ Δ : F.Ctx m} → AxiomSettled temp (Γ ⊩ sub Δ)
      gensub-runit : ∀ {temp} {Γ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable temp rhs}} → AxiomSettled temp (Γ ⊩ rhs)
      gensub-assoc : ∀ {temp} {Γ Δ Θ : F.Ctx m} {rhs : F.RHS m} {{u : F.Substitutable temp rhs}} → AxiomSettled temp (Γ ⊩ rhs)
      -- mixWhiskerL t ∘ mixWhiskerR s = mixWhiskerR s ∘ mixWhiskerL (t [ Γ.s ])
      -- We cannot yet state this, because we cannot substitute t in the cold model.
      -- This will be added together with the custom rules that can also refer to substitution.
      --gensub-mixWhiskerLR : ∀ {temp} {Γ Δ : F.Ctx m} {Φ Ψ : Junctor m n} → AxiomSettled temp (Γ F.:⦊ Φ ⊩ sub (Δ F.:⦊ Ψ))
      -- mixWhiskerL (whiskerR t) = mixWhiskerR (mixWhiskerL t)
      mixWhiskerL-whiskerR : ∀ {temp} {m n o : Mode} {Γ : F.Ctx m} {Φ Ψ : Junctor m n} {Ξ : Junctor n o}
        → AxiomSettled temp (Γ F.:⦊ (Φ ⦊ Ξ) ⊩ sub (Γ F.:⦊ (Ψ ⦊ Ξ)))
      -- mixWhiskerL respects idJHom and compJHom
      mixWhiskerL-idJHom : ∀ {temp} {m n : Mode} {Γ : F.Ctx m} {Φ : Junctor m n}
        → AxiomSettled temp ((Γ F.:⦊ Φ) ⊩ sub (Γ F.:⦊ Φ))
      mixWhiskerL-compJHom : ∀ {temp} {m n : Mode} {Γ : F.Ctx m} {Φ Ψ Ξ : Junctor m n}
        → AxiomSettled temp ((Γ F.:⦊ Φ) ⊩ sub (Γ F.:⦊ Ξ))
      -- mixWhiskerR respects idsub and compsub
      mixWhiskerR-idsub : ∀ {temp} {m n : Mode} {Γ : F.Ctx m} {Φ : Junctor m n}
        → AxiomSettled temp ((Γ F.:⦊ Φ) ⊩ sub (Γ F.:⦊ Φ))
      mixWhiskerR-compsub : ∀ {temp} {m n : Mode} {Γ Δ Θ : F.Ctx m} {Φ : Junctor m n}
        → AxiomSettled temp ((Γ F.:⦊ Φ) ⊩ sub (Θ F.:⦊ Φ))
      -- mixWhiskerL respects :⦊
      mixWhiskerL-:⦊ : ∀ {temp} {m n o : Mode} {Γ : F.Ctx m} {Φ : Junctor m n} {Ψ Ξ : Junctor n o}
        → AxiomSettled temp ((Γ F.:⦊ Φ) F.:⦊ Ψ ⊩ sub ((Γ F.:⦊ Φ) F.:⦊ Ξ))
      -- mixWhiskerR respects ◇ and ⦊
      mixWhiskerR-◇ : ∀ {temp} {m : Mode} {Γ Δ : F.Ctx m}
        → AxiomSettled temp (Γ F.:⦊ ◇ ⊩ sub (Δ F.:⦊ ◇))
      mixWhiskerR-⦊ : ∀ {temp} {m n o : Mode} {Γ Δ : F.Ctx m} {Φ : Junctor m n} {Ψ : Junctor n o}
        → AxiomSettled temp (Γ F.:⦊ (Φ ⦊ Ψ) ⊩ sub (Δ F.:⦊ (Φ ⦊ Ψ)))

    AxiomCold = AxiomSettled cold
    AxiomHot = AxiomSettled hot

    arityAxiomSettled : ∀ {temp} {J} → AxiomSettled temp J → Arity
    arityAxiomSettled (gensub-inctx {m} {Γ} {Δ} {rhs} o) = (Γ ⊩ sub Δ) ∷ translateAritySettled cmatfnd Δ (arity o)
    arityAxiomSettled (gensub-lunit {temp} {m}{Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomSettled (gensub-runit {temp} {m}{Γ}{rhs}) = (Γ ⊩ rhs) ∷ []
    arityAxiomSettled (gensub-assoc {temp} {m}{Γ}{Δ}{Θ}{rhs}) = (Θ ⊩ rhs) ∷ (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
    --arityAxiomSettled (gensub-mixWhiskerLR {temp} {m}{n} {Γ}{Δ}{Φ}{Ψ}) = (Δ ⊩ jhom Φ Ψ) ∷ (Γ ⊩ sub Δ) ∷ []
    arityAxiomSettled (mixWhiskerL-whiskerR {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) = (Γ ⊩ jhom Φ Ψ) ∷ []
    arityAxiomSettled (mixWhiskerL-idJHom {temp} {m}{n} {Γ}{Φ}) = []
    arityAxiomSettled (mixWhiskerL-compJHom {temp} {m}{n} {Γ}{Φ}{Ψ}{Ξ}) = (Γ ⊩ jhom Ψ Ξ) ∷ (Γ ⊩ jhom Φ Ψ) ∷ []
    arityAxiomSettled (mixWhiskerR-idsub {temp} {m}{n} {Γ}{Φ}) = []
    arityAxiomSettled (mixWhiskerR-compsub {temp} {m}{n} {Γ}{Δ}{Θ}{Φ}) = (Δ ⊩ sub Θ) ∷ (Γ ⊩ sub Δ) ∷ []
    arityAxiomSettled (mixWhiskerL-:⦊ {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) = (Γ F.:⦊ Φ ⊩ jhom Ψ Ξ) ∷ []
    arityAxiomSettled (mixWhiskerR-◇ {temp} {m} {Γ}{Δ}) = (Γ ⊩ sub Δ) ∷ []
    arityAxiomSettled (mixWhiskerR-⦊ {temp} {m}{n}{o} {Γ}{Δ}{Φ}{Ψ}) = (Γ ⊩ sub Δ) ∷ []

    lhsAxiomSettled rhsAxiomSettled : ∀ {temp} {J} → (axiom : AxiomSettled temp J)
      → TermF temp (mtyp (arity2mset (arityAxiomSettled axiom))) J
    lhsAxiomSettled (gensub-inctx {m} {Γ} {Δ} {rhs} o) =
      (inctx o $1 tabulateOverLookup (aritySettled {hot} (inctx o)) (arvarF _ ∘ suc)) [ arvarF _ zero ]1
    lhsAxiomSettled gensub-lunit = (idsub $1 []) [ arvarF _ zero ]1
    lhsAxiomSettled gensub-runit = arvarF _ zero [ idsub $1 [] ]1
    lhsAxiomSettled gensub-assoc = arvarF _ zero [ arvarF _ one ]1 [ arvarF _ two ]1
    --lhsAxiomSettled (gensub-mixWhiskerLR {temp} {m}{n} {Γ}{Δ}{Φ}{Ψ}) =
    --  (mixWhiskerL Δ $1 arvarF _ zero ∷ []) [ mixWhiskerR Φ $1 arvarF _ one ∷ [] ]1
    lhsAxiomSettled (mixWhiskerL-whiskerR {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      mixWhiskerL Γ $1 (inctx (whiskerR Ξ) $1 substCtx⁻ (F.:⦊IdR Γ) (arvarF _ zero) ∷ []) ∷ []
    lhsAxiomSettled (mixWhiskerL-idJHom {temp} {m}{n} {Γ}{Φ}) =
      mixWhiskerL Γ $1 (inctx idJHom $1 []) ∷ []
    lhsAxiomSettled (mixWhiskerL-compJHom {temp} {m}{n} {Γ}{Φ}{Ψ}{Ξ}) =
      mixWhiskerL Γ $1 (inctx compJHom $1
        substCtx⁻ (F.:⦊IdR Γ) (arvarF _ zero) ∷
        substCtx⁻ (F.:⦊IdR Γ) (arvarF _ one) ∷ []) ∷ []
    lhsAxiomSettled (mixWhiskerR-idsub {temp} {m}{n} {Γ}{Φ}) =
      mixWhiskerR Φ $1 (idsub $1 []) ∷ []
    lhsAxiomSettled (mixWhiskerR-compsub {temp} {m}{n} {Γ}{Δ}{Θ}{Φ}) =
      mixWhiskerR Φ $1 (compsub $1 arvarF _ zero ∷ arvarF _ one ∷ []) ∷ []
    lhsAxiomSettled (mixWhiskerL-:⦊ {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      mixWhiskerL (Γ F.:⦊ Φ) $1 arvarF _ zero ∷ []
    lhsAxiomSettled (mixWhiskerR-◇ {temp} {m} {Γ}{Δ}) =
      mixWhiskerR ◇ $1 arvarF _ zero ∷ []
    lhsAxiomSettled (mixWhiskerR-⦊ {temp} {m}{n}{o} {Γ}{Δ}{Φ}{Ψ}) =
      mixWhiskerR (Φ ⦊ Ψ) $1 arvarF _ zero ∷ []

    rhsAxiomSettled (gensub-inctx {m} {Γ} {Δ} {rhs} o) =
      inctx o $1 mapOverSpan
        {B = TermF hot (mtyp (arity2mset ((Γ ⊩ sub Δ) ∷ translateAritySettled cmatfnd Δ (arity o))))}
        {B' = TermF hot (mtyp (arity2mset (arityAxiomSettled {hot} (gensub-inctx o))))}
        (translateJudSettled cmatfnd Δ)
        (translateJudSettled cmatfnd Γ)
        (λ J x → x [ mixWhiskerR _ $1 arvarF _ zero ∷ [] ]1)
        (arity o)
        (tabulateOverLookup (aritySettled {hot} (inctx o)) (arvarF _ ∘ suc))
    rhsAxiomSettled gensub-lunit = arvarF _ zero
    rhsAxiomSettled gensub-runit = arvarF _ zero
    rhsAxiomSettled gensub-assoc = arvarF _ zero [ arvarF _ one [ arvarF _ two ]1 ]1
    --rhsAxiomSettled (gensub-mixWhiskerLR {temp} {m}{n} {Γ}{Δ}{Φ}{Ψ}) =
    --  (mixWhiskerR Ψ $1 arvarF _ one ∷ []) [ mixWhiskerL Γ $1 {!? [ ? ]1!} ∷ [] ]1
    rhsAxiomSettled (mixWhiskerL-whiskerR {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      substCtxRHS⁻ (sym (F.:⦊Assoc Γ Φ Ξ)) (cong sub (sym (F.:⦊Assoc Γ Ψ Ξ))) (
        mixWhiskerR Ξ $1 (mixWhiskerL Γ $1 arvarF _ zero ∷ []) ∷ []
      )
    rhsAxiomSettled (mixWhiskerL-idJHom {temp} {m}{n} {Γ}{Φ}) = idsub $1 []
    rhsAxiomSettled (mixWhiskerL-compJHom {temp} {m}{n} {Γ}{Φ}{Ψ}{Ξ}) = compsub $1
      (mixWhiskerL Γ $1 arvarF _ zero ∷ []) ∷
      (mixWhiskerL Γ $1 arvarF _ one ∷ []) ∷ []
    rhsAxiomSettled (mixWhiskerR-idsub {temp} {m}{n} {Γ}{Φ}) = idsub $1 []
    rhsAxiomSettled (mixWhiskerR-compsub {temp} {m}{n} {Γ}{Δ}{Θ}{Φ}) = compsub $1
      (mixWhiskerR Φ $1 arvarF _ zero ∷ []) ∷
      (mixWhiskerR Φ $1 arvarF _ one ∷ []) ∷ []
    rhsAxiomSettled (mixWhiskerL-:⦊ {temp} {m}{n}{o} {Γ}{Φ}{Ψ}{Ξ}) =
      substCtxRHS⁻ (F.:⦊Assoc Γ Φ Ψ) (cong sub (F.:⦊Assoc Γ Φ Ξ)) (
        mixWhiskerL Γ $1 (inctx (whiskerL Φ) $1 arvarF _ zero ∷ []) ∷ []
      )
    rhsAxiomSettled (mixWhiskerR-◇ {temp} {m} {Γ}{Δ}) =
      substCtxRHS⁻ (F.:⦊IdR Γ) (cong sub (F.:⦊IdR Δ)) (arvarF _ zero)
    rhsAxiomSettled (mixWhiskerR-⦊ {temp} {m}{n}{o} {Γ}{Δ}{Φ}{Ψ}) =
      substCtxRHS⁻ (sym (F.:⦊Assoc Γ Φ Ψ)) (cong sub (sym (F.:⦊Assoc Δ Φ Ψ))) (
        mixWhiskerR Ψ $1 (mixWhiskerR Φ $1 arvarF _ zero ∷ []) ∷ []
      )

    eqTheorySettled : (temp : Temp) → MatEqTheory (fmatSettled temp)
    Axiom (eqTheorySettled temp) = AxiomSettled temp
    msetArity (eqTheorySettled temp) = arity2mset ∘ arityAxiomSettled
    lhs (eqTheorySettled temp) = lhsAxiomSettled
    rhs (eqTheorySettled temp) = rhsAxiomSettled

    eqTheoryCold = eqTheorySettled cold
    eqTheoryHot = eqTheorySettled hot

    matSettled : Temp → Mat (matsigSettled cmatfnd)
    Mat.getFreeMat (matSettled temp) = fmatSettled temp
    Mat.getMatEqTheory (matSettled temp) = eqTheorySettled temp

    matCold = matSettled cold
    matHot = matSettled hot
