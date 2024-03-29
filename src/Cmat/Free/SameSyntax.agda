{-# OPTIONS --cubical --type-in-type --experimental-lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinData
open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.EilenbergMoore

open import Mat.Signature
open import Mat.Free.Presentation
open import Mat.Free.Term
open import Mat.Free.Model
open import Mat.Presentation
open import Mat.Term
open import Mat.Model
open import Cmat.Signature
open import Cmat.Free.Presentation

module Cmat.Free.SameSyntax where

-- The common signature
module CommonSignature {cmatsig : CmatSignature} (cmatfnd : CmatSignature.CmatFoundation cmatsig) where

  open CmatSignature cmatsig
  open CmatFoundation cmatfnd

  matsig : MatSignature
  matsig = matsigSettled cmatfnd

  open MatSignature matsig

  {- Let X and S be multisorted sets of signature matsig.
     Then S defines a category of contexts and substitutions.
     We define the free mode- and type-indexed S-presheaf over X.
     This is akin to Fiore & Szamozvancev's substitution tensor S ⊙ X,
     except that we don't assume a priori that S and X are renamable.
     Hence, we need not take an end.
  -}
  data FreeTypedPsh (S X : MType) : MType where
    _[_]Free : ∀ {m : Mode} {Γ Δ : Ctx m} {rhs : RHS m} → X (Δ ⊩ rhs) → S (Γ ⊩ sub Δ) → FreeTypedPsh S X (Γ ⊩ rhs)

  msetFreeTypedPsh : (msetS msetX : MSet) → MSet
  fst (msetFreeTypedPsh msetS msetX J) = FreeTypedPsh (mtyp msetS) (mtyp msetX) J
  snd (msetFreeTypedPsh msetS msetX J) = {!!}

  {- Analogously, we we consider the cofree mode- and type-indexed S-presheaf over X.
     This is akin to Fiore & Szamozvancev's substitution exponential ⦗_,_⦘.
  -}
  record CofreeTypedPsh (S X : MType) (J : Jud cmatfnd) : Type where
    eta-equality
    constructor mkCofree
    open Jud J
    field
      _[_⊢_]Cofree : (Δ : Ctx jud'mode) → S (Δ ⊩ sub jud'ctx) → X (Δ ⊩ jud'rhs)
  open CofreeTypedPsh public

  isSetCofreeTypedPsh : (msetS msetX : MSet) → ∀ J → isSet (CofreeTypedPsh (mtyp msetS) (mtyp msetX) J)
  isSetCofreeTypedPsh msetS msetX J = isOfHLevelRetractFromIso 2 i (isSetΠ λ Δ → isSetΠ λ σ → snd (msetX _))
    where unquoteDecl i = declareRecordIsoΣ i (quote CofreeTypedPsh)

  msetCofreeTypedPsh : (msetS msetX : MSet) → MSet
  fst (msetCofreeTypedPsh msetS msetX J) = CofreeTypedPsh (mtyp msetS) (mtyp msetX) J
  snd (msetCofreeTypedPsh msetS msetX J) = isSetCofreeTypedPsh msetS msetX J

module NoCat {cmatsig : CmatSignature} (cmatfnd : CmatSignature.CmatFoundation cmatsig) (fcmat : FreeCmat cmatsig) where

  open CmatSignature cmatsig
  open CmatFoundation cmatfnd
  open CommonSignature cmatfnd
  open MatSignature matsig
  open FreeMat {matsig}
  open TermF {matsig}
  open FreeCmat fcmat renaming (arity to carity)

  open Category hiding (_∘_)
  open Functor
  open NaturalBijection
  open _⊣_
  open AlgebraHom

  module _ (msetX : MSet) where

    TermHot : MType
    TermHot = TermQ (matHot cmatfnd) (mtyp msetX)

    msetHot : MSet
    msetHot = msetTermQ (matHot cmatfnd) msetX

    private
      testHot : TermHot ≡ mtyp msetHot
      testHot = refl

    SubstX : MType
    SubstX = FreeTypedPsh TermHot (mtyp msetX)

    TermCold : MType
    TermCold = TermF (fmatCold cmatfnd) SubstX

    msetSubstX : MSet
    msetSubstX = msetFreeTypedPsh msetHot msetX

    msetCold : MSet
    msetCold = msetTermF (fmatCold cmatfnd) msetSubstX

    private
      testCold : TermCold ≡ mtyp msetCold
      testCold = refl

    ------------------------------
    -- Mapping from cold to hot --
    ------------------------------

    -- Just use an opmap and an axmap

{-
    -- msetHot is an algebra for Term1 cold
    isColdAlg1-msetHot : IsAlgebra (ftrTerm1 (fmatCold cmatfnd)) msetHot
    isColdAlg1-msetHot J (term1 o args) = join1Q (term1 (cold o) args)

    coldAlg1-msetHot : Algebra (ftrTerm1 (fmatCold cmatfnd))
    coldAlg1-msetHot = algebra msetHot isColdAlg1-msetHot

    -- msetHot is an EM-algebra for TermF cold
    -- instead prove that inverses are adjoint in the cubical library and compose adjunctions
    coldEMAlgF-msetHot : EMAlgebra (monadTermF (fmatCold cmatfnd))
    coldEMAlgF-msetHot = model1→F (fmatCold cmatfnd) coldAlg1-msetHot

    -- we can handle leaves
    substX→termHot : ∀ J → SubstX J → TermHot J
    substX→termHot J (x [ σ ]Free) = join1Q (term1 gensub (varQ x ∷ σ ∷ []))

    -- same but viewed as a morphism of MSets
    msetHom-substX→termHot : catMSet [ msetSubstX , msetHot ]
    msetHom-substX→termHot = substX→termHot

    -- transpose the morphism under ftrFreeModelF ⊣ ftrForgetModelF
    emalgHom-termCold→termHot :
      catModelF (fmatCold cmatfnd) [ ftrFreeModelF (fmatCold cmatfnd) ⟅ msetSubstX ⟆ , coldEMAlgF-msetHot ]
    emalgHom-termCold→termHot = _♯ (adjModelF (fmatCold cmatfnd)) {msetSubstX} {coldEMAlgF-msetHot} substX→termHot

    -- extract
    termCold→termHot : ∀ J → TermCold J → TermHot J
    termCold→termHot = carrierHom emalgHom-termCold→termHot
-}

    --------------------------------------------------
    -- Mapping from hot to cold with an environment --
    --------------------------------------------------

    -- Adding the environment
    EnvirCold : MType
    EnvirCold = CofreeTypedPsh TermCold TermCold

    msetEnvirCold : MSet
    msetEnvirCold = msetCofreeTypedPsh msetCold msetCold

    private
      testEnvirCold : mtyp msetEnvirCold ≡ EnvirCold
      testEnvirCold = refl

{-
    -- msetEnvirCold is an algebra for Term1 hot
    isHotAlg1-msetEnvirCold : IsAlgebra (ftrTerm1 (fmatHot cmatfnd)) msetEnvirCold
    isHotAlg1-msetEnvirCold J (term1 (gensub) (t ∷ τ ∷ [])) [ Δ ⊢ σ ]Cofree = t [ _ ⊢ τ [ _ ⊢ σ ]Cofree ]Cofree
    isHotAlg1-msetEnvirCold J (term1 (cold (inctx {m} {Γ} o)) args) [ Δ ⊢ σ ]Cofree =
      inctx o $1 mapOverSpan
        (translateJudSettled cmatfnd Γ)
        (translateJudSettled cmatfnd Δ)
        (λ J' tCofree → tCofree [ _ ⊢ mixWhiskerR _ $1 σ ∷ (idsub $1 []) ∷ [] ]Cofree)
        (carity o)
        args
    isHotAlg1-msetEnvirCold J (term1 (cold (idsub)) []) [ Δ ⊢ σ ]Cofree = σ
    --isHotAlg1-msetEnvirCold J (term1 (cold (compsub)) (ρ ∷ τ ∷ [])) [ Δ ⊢ σ ]Cofree =
    --  compsub $1 ρ [ _ ⊢ idsub $1 [] ]Cofree ∷ (τ [ _ ⊢ σ ]Cofree) ∷ []
    isHotAlg1-msetEnvirCold J (term1 (cold (mixWhiskerL Θ)) (ρ ∷ τ ∷ [])) [ Δ ⊢ σ ]Cofree =
      mixWhiskerL Θ $1 (ρ [ _ ⊢ idsub $1 [] ]Cofree) ∷ (τ [ _ ⊢ σ ]Cofree) ∷ []
    isHotAlg1-msetEnvirCold J (term1 (cold (mixWhiskerR Ξ)) (ρ ∷ τ ∷ [])) [ Δ ⊢ σ ]Cofree =
      mixWhiskerR Ξ $1 (ρ [ _ ⊢ idsub $1 [] ]Cofree) ∷ (τ [ _ ⊢ σ ]Cofree) ∷ []

    hotAlg1-msetEnvirCold : Algebra (ftrTerm1 (fmatHot cmatfnd))
    hotAlg1-msetEnvirCold = algebra msetEnvirCold isHotAlg1-msetEnvirCold

    -- msetEnvirCold respects the equational theory for Term1 hot

    respectsEqTheory1-msetEnvirCold : respectsEqTheory1 (matHot cmatfnd) hotAlg1-msetEnvirCold
    respectsEqTheory1-msetEnvirCold (gensub-inctx {m}{Γ}{Δ}{rhs} o) f =
      cong mkCofree (funExt λ Ω → funExt λ σ → congS (inctx o $1_) (
        _
          ≡⟨ sym (mapOverSpan∘Idfun
               (translateJudSettled cmatfnd Δ)
               (translateJudSettled cmatfnd Ω)
               _
               _
               (carity o)
             ) ≡$ _ ⟩
        _
          ≡⟨ sym (mapOverSpan∘Idfun
               (translateJudSettled cmatfnd Δ)
               (translateJudSettled cmatfnd Ω)
               _
               _
               (carity o)
             ) ≡$ _ ⟩
        _
          ≡⟨ congS (λ g → mapOverSpan
               (translateJudSettled cmatfnd Δ)
               (translateJudSettled cmatfnd Ω)
               g
               (carity o)
               (tabulateOverLookup (arityCold cmatfnd (inctx o)) λ p → arvarF (fmatHot cmatfnd) (suc p))
             ) (
               funExt λ J → funExt λ t → congS (λ σ → _[_⊢_]Cofree
                 (model1→F-algStr
                   (fmatHot cmatfnd)
                   hotAlg1-msetEnvirCold
                   (translateJudSettled cmatfnd Δ J)
                   (mapTermF (fmatHot cmatfnd) f (translateJudSettled cmatfnd Δ J) t)
                   )
                 _
                 σ) {!!}
                 {-
                 Write τ for f zero
                 Then we have:
                 LHS: (τ [ σ ]Cof * _)[ id ]
                 RHS: (τ [ id ]Cof * _)[ (σ * _)[ id ] ]
                 -}
             ) ⟩
        _
          ≡⟨ mapOverSpan-∘
               (translateJudSettled cmatfnd Δ)
               (translateJudSettled cmatfnd Γ)
               (translateJudSettled cmatfnd Ω)
               _
               _
               (carity o)
             ≡$ _ ⟩
        _
          ≡⟨ mapOverSpan∘Idfun
               (translateJudSettled cmatfnd Γ)
               (translateJudSettled cmatfnd Ω)
               _
               _
               (carity o)
             ≡$ _ ⟩
        _
          ≡⟨ mapOverSpan∘Idfun
               (translateJudSettled cmatfnd Γ)
               (translateJudSettled cmatfnd Ω)
               _
               _
               (carity o)
             ≡$ _ ⟩
        _ ∎
      ))
    --respectsEqTheory1-msetEnvirCold (gensub-mixWhiskerL Θ) f = refl
    --respectsEqTheory1-msetEnvirCold (gensub-mixWhiskerR Ξ) f = refl
    respectsEqTheory1-msetEnvirCold gensub-lunit f = refl
    respectsEqTheory1-msetEnvirCold gensub-runit f = refl
    respectsEqTheory1-msetEnvirCold gensub-assoc f = refl
-}
