{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct renaming (_×_ to _×C_)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Reflection.RecordEquiv

open import Mat.Signature

module Cmat.Signature where

open Category
open Functor

{- Instantiators should see to it that the mode can be inferred
   from the type of junctors/customRHS. -}
record CmatSignature : Type where
  no-eta-equality
  field
    catModeJunctor : Category _ _

  Mode : Type
  Mode = ob catModeJunctor

  field
    isGroupoidMode : isGroupoid Mode
    CustomRHS : Mode → Type
    isGroupoidCustomRHS : ∀ {m} → isGroupoid (CustomRHS m)

  private
    variable
      m n p : Mode

  Junctor : Mode → Mode → Type
  Junctor = Hom[_,_] catModeJunctor

  isSetJunctor : isSet (Junctor m n)
  isSetJunctor = isSetHom catModeJunctor

  _⦊_ : Junctor m n → Junctor n p → Junctor m p
  Φ ⦊ Ψ = Φ ⋆⟨ catModeJunctor ⟩ Ψ

  infixl 6 _⦊_

  ◇ : Junctor m m
  ◇ = id catModeJunctor

  data RHS' (X : Mode → Type) (m : Mode) : Type where
    custom : (crhs : X m) → RHS' X m
    jhom : ∀ {n} → (Ψ Φ : Junctor m n) → RHS' X m

  mapRHS' : ∀ {X Y : Mode → Type} → (f : ∀ m → X m → Y m) → RHS' X m → RHS' Y m
  mapRHS' f (custom crhs) = custom (f _ crhs)
  mapRHS' f (jhom Ψ Φ) = jhom Ψ Φ

  RHS : Mode → Type
  RHS m = RHS' CustomRHS m

  module _ where
    open _≅_

    RepRHS : Mode → Type
    RepRHS m = CustomRHS m ⊎ (Σ[ n ∈ Mode ] Junctor m n × Junctor m n)

    toRepRHS : ∀ {m} → RHS m → RepRHS m
    toRepRHS (custom crhs) = inl crhs
    toRepRHS (jhom Ψ Φ) = inr (_ , Ψ , Φ)

    fromRepRHS : ∀ {m} → RepRHS m → RHS m
    fromRepRHS (inl crhs) = custom crhs
    fromRepRHS (inr (n , Ψ , Φ)) = jhom Ψ Φ

    fromToRepRHS : ∀ {m} (rhs : RHS m) → fromRepRHS (toRepRHS rhs) ≡ rhs
    fromToRepRHS (custom x) = refl
    fromToRepRHS (jhom Ψ Φ) = refl

    toFromRepRHS : ∀ {m} (rrhs : RepRHS m) → toRepRHS (fromRepRHS rrhs) ≡ rrhs
    toFromRepRHS (inl x) = refl
    toFromRepRHS (inr x) = refl

    isoRepRHS : ∀ {m} → RHS m ≅ RepRHS m
    fun isoRepRHS = toRepRHS
    inv isoRepRHS = fromRepRHS
    rightInv isoRepRHS = toFromRepRHS
    leftInv isoRepRHS = fromToRepRHS

    isGroupoidRepRHS : ∀ {m} → isGroupoid (RepRHS m)
    isGroupoidRepRHS =
        isOfHLevel⊎ 1 isGroupoidCustomRHS (
        isOfHLevelΣ 3 isGroupoidMode λ n → isOfHLevel× 3 (isSet→isGroupoid isSetJunctor) (isSet→isGroupoid isSetJunctor)
      )

  isGroupoidRHS : isGroupoid (RHS m)
  isGroupoidRHS = isOfHLevelRetractFromIso 3 isoRepRHS isGroupoidRepRHS

  module _ {{terminalModeJunctor : Terminal catModeJunctor}} where
    m⊤ : Mode
    m⊤ = fst terminalModeJunctor
    isTerminal-m⊤ : isTerminal catModeJunctor m⊤
    isTerminal-m⊤ = snd terminalModeJunctor

    pshCtx : Functor catModeJunctor (SET _)
    pshCtx = funcComp (HomFunctor catModeJunctor) (rinj (catModeJunctor ^op) catModeJunctor m⊤)

    ◆ : ∀ {m} → Junctor m m⊤
    ◆ = fst (isTerminal-m⊤ _)

    ◆η : ∀ {m} → (Φ : Junctor m m⊤) → Φ ≡ ◆
    ◆η Φ = sym (snd (isTerminal-m⊤ _) Φ)

    Ctx : Mode → Type
    Ctx m = fst (F-ob pshCtx m)

    isSetCtx : isSet (Ctx m)
    isSetCtx {m} = snd (F-ob pshCtx m)

    _⦊'_ : Ctx m → Junctor m n → Ctx n
    Γ ⦊' Ψ = Γ ⦊ Ψ

    infixl 6 _⦊'_

    -- A substitution `Δ ⊢ sub Γ` is a junctor morphism `Δ ⊢ jhom ◇ (◆ ⦊ Γ)`
    -- from the identity junctor `◇` to the constant junctor on `Γ`.
    sub : ∀ {m} → Ctx m → RHS m
    sub Γ = jhom ◇ (◆ ⦊ Γ)

  record Jud (m0 : Mode) : Type where
    constructor _⊩_
    field
      {jud'mode} : Mode
      jud'ctx : Junctor m0 jud'mode
      jud'rhs : RHS jud'mode

  pattern _⊢_ Γ crhsT = Γ ⊩ custom crhsT

  infix 5 _⊩_ _⊢_

  module _ (m0 : Mode) where
    open _≅_

    RepJud : Type
    RepJud = Σ[ m ∈ Mode ] Σ[ Γ ∈ Junctor m0 m ] RHS m

    private
      unquoteDecl isoRepJud' = declareRecordIsoΣ isoRepJud' (quote Jud)

    isoRepJud : Jud m0 ≅ RepJud
    isoRepJud = isoRepJud'

    isGroupoidRepJud : isGroupoid RepJud
    isGroupoidRepJud = isOfHLevelΣ 3 isGroupoidMode λ m → isOfHLevelΣ 3 (isSet→isGroupoid isSetJunctor) (λ _ → isGroupoidRHS)

  isGroupoidJud : ∀ {m0} → isGroupoid (Jud m0)
  isGroupoidJud {m0} = isOfHLevelRetractFromIso 3 (isoRepJud m0) (isGroupoidRepJud m0)

  -- contextual arity
  CArity' : (Mode → Type) → Mode → Type
  CArity' X m = List (Σ[ n ∈ Mode ] Junctor m n × RHS' X n)

  mapCArity' : ∀ {X Y : Mode → Type} → (f : ∀ m → X m → Y m) → CArity' X m → CArity' Y m
  mapCArity' f [] = []
  mapCArity' f ((n , Φ , rhs) ∷ arity) = (n , Φ , mapRHS' f rhs) ∷ mapCArity' f arity

  CArity : Mode → Type
  CArity m = List (Σ[ n ∈ Mode ] Junctor m n × RHS n)

  isGroupoidCArity : ∀ {m} → isGroupoid (CArity m)
  isGroupoidCArity =
    isOfHLevelList 1 (
    isOfHLevelΣ 3 isGroupoidMode (λ n →
    isOfHLevel× 3 (isSet→isGroupoid isSetJunctor) isGroupoidRHS))

  module _ where
    open MatSignature

    {- The signature of the MAT translation.
    -}
    matsigPlant : Mode → MatSignature
    Sort (matsigPlant m0) = Jud m0
    isGroupoidSort (matsigPlant m0) = isGroupoidJud

    plantArity : ∀ {m0 m} (Γ : Junctor m0 m) → CArity m → Arity (matsigPlant m0)
    plantArity Γ [] = []
    plantArity Γ ((n , Φ , rhs) ∷ arity) = (Γ ⦊ Φ ⊩ rhs) ∷ plantArity Γ arity
