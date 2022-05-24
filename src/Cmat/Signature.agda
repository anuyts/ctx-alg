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
open import Cubical.Reflection.RecordEquiv

open import Mat.Signature

module Cmat.Signature where

open Category
open Functor

{- Instantiators should see to it that the mode can be inferred
   from the type of contexts/customRHSs. -}
record CmatSignature : Type where
  no-eta-equality
  field
    catModeJunctor : Category _ _
    pshCtx : Functor catModeJunctor (SET _)

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

  Ctx : Mode → Type
  Ctx m = fst (F-ob pshCtx m)

  isSetCtx : isSet (Ctx m)
  isSetCtx {m} = snd (F-ob pshCtx m)

  _⦊_ : Ctx m → Junctor m n → Ctx n
  Γ ⦊ Ψ = F-hom pshCtx Ψ Γ

  ◆ : Junctor m m
  ◆ = id catModeJunctor

  _⦊'_ : Junctor m n → Junctor n p → Junctor m p
  Φ ⦊' Ψ = Φ ⋆⟨ catModeJunctor ⟩ Ψ

  infixl 6 _⦊_

  data RHS' (X : Mode → Type) (m : Mode) : Type where
    custom : (crhs : X m) → RHS' X m
    sub : (Γ : Ctx m) → RHS' X m
    jhom : ∀ {n} → (Ψ Φ : Junctor m n) → RHS' X m

  mapRHS' : ∀ {X Y : Mode → Type} → (f : ∀ m → X m → Y m) → RHS' X m → RHS' Y m
  mapRHS' f (custom crhs) = custom (f _ crhs)
  mapRHS' f (sub Γ) = sub Γ
  mapRHS' f (jhom Ψ Φ) = jhom Ψ Φ

  RHS : Mode → Type
  RHS m = RHS' CustomRHS m

  module _ where
    open _≅_

    RepRHS : Mode → Type
    RepRHS m = CustomRHS m ⊎ (Ctx m ⊎ (Σ[ n ∈ Mode ] Junctor m n × Junctor m n))

    toRepRHS : ∀ {m} → RHS m → RepRHS m
    toRepRHS (custom crhs) = inl crhs
    toRepRHS (sub Γ) = inr (inl Γ)
    toRepRHS (jhom Ψ Φ) = inr (inr (_ , Ψ , Φ))

    fromRepRHS : ∀ {m} → RepRHS m → RHS m
    fromRepRHS (inl crhs) = custom crhs
    fromRepRHS (inr (inl Γ)) = sub Γ
    fromRepRHS (inr (inr (n , Ψ , Φ))) = jhom Ψ Φ

    fromToRepRHS : ∀ {m} (rhs : RHS m) → fromRepRHS (toRepRHS rhs) ≡ rhs
    fromToRepRHS (custom x) = refl
    fromToRepRHS (sub x) = refl
    fromToRepRHS (jhom Ψ Φ) = refl

    toFromRepRHS : ∀ {m} (rrhs : RepRHS m) → toRepRHS (fromRepRHS rrhs) ≡ rrhs
    toFromRepRHS (inl x) = refl
    toFromRepRHS (inr (inl x)) = refl
    toFromRepRHS (inr (inr x)) = refl

    isoRepRHS : ∀ {m} → RHS m ≅ RepRHS m
    fun isoRepRHS = toRepRHS
    inv isoRepRHS = fromRepRHS
    rightInv isoRepRHS = toFromRepRHS
    leftInv isoRepRHS = fromToRepRHS

    isGroupoidRepRHS : ∀ {m} → isGroupoid (RepRHS m)
    isGroupoidRepRHS =
        isOfHLevel⊎ 1 isGroupoidCustomRHS (
        isOfHLevel⊎ 1 (isSet→isGroupoid isSetCtx) (
        isOfHLevelΣ 3 isGroupoidMode λ n → isOfHLevel× 3 (isSet→isGroupoid isSetJunctor) (isSet→isGroupoid isSetJunctor)
      ))

  isGroupoidRHS : isGroupoid (RHS m)
  isGroupoidRHS = isOfHLevelRetractFromIso 3 isoRepRHS isGroupoidRepRHS

  record Jud : Type where
    constructor _⊩_
    field
      {jud'mode} : Mode
      jud'ctx : Ctx jud'mode
      jud'rhs : RHS jud'mode

  pattern _⊢_ Γ crhsT = Γ ⊩ custom crhsT
  
  infix 5 _⊩_ _⊢_

  module _ where
    open _≅_

    RepJud : Type
    RepJud = Σ[ m ∈ Mode ] Σ[ Γ ∈ Ctx m ] RHS m

    private
      unquoteDecl isoRepJud' = declareRecordIsoΣ isoRepJud' (quote Jud)

    isoRepJud : Jud ≅ RepJud
    isoRepJud = isoRepJud'

    isGroupoidRepJud : isGroupoid RepJud
    isGroupoidRepJud = isOfHLevelΣ 3 isGroupoidMode λ m → isOfHLevelΣ 3 (isSet→isGroupoid isSetCtx) (λ _ → isGroupoidRHS)

  isGroupoidJud : isGroupoid Jud
  isGroupoidJud = isOfHLevelRetractFromIso 3 isoRepJud isGroupoidRepJud

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
    matsigPlant : MatSignature
    Sort matsigPlant = Jud
    isGroupoidSort matsigPlant = isGroupoidJud

    plantArity : ∀ {m} (Γ : Ctx m) → CArity m → Arity matsigPlant
    plantArity Γ [] = []
    plantArity Γ ((n , Φ , rhs) ∷ arity) = (Γ ⦊ Φ ⊩ rhs) ∷ plantArity Γ arity

{- The signature of the open translation.
-}
module _ (cmatsig : CmatSignature) where

  open CmatSignature

  data OpenCustomRHS (m : Mode cmatsig) : Type where
    custom : (crhs : CustomRHS cmatsig m) → OpenCustomRHS m
    sub : (Γ : Ctx cmatsig m) → OpenCustomRHS m

  module _ where
    open _≅_

    RepOpenCustomRHS : Mode cmatsig → Type
    RepOpenCustomRHS m = CustomRHS cmatsig m ⊎ Ctx cmatsig m

    toRepOpenCustomRHS : ∀ {m} → OpenCustomRHS m → RepOpenCustomRHS m
    toRepOpenCustomRHS (custom crhs) = inl crhs
    toRepOpenCustomRHS (sub Γ) = inr Γ

    fromRepOpenCustomRHS : ∀ {m} → RepOpenCustomRHS m → OpenCustomRHS m
    fromRepOpenCustomRHS (inl x) = custom x
    fromRepOpenCustomRHS (inr x) = sub x

    fromToRepOpenCustomRHS : ∀ {m} (ocrhs : OpenCustomRHS m) → fromRepOpenCustomRHS (toRepOpenCustomRHS ocrhs) ≡ ocrhs
    fromToRepOpenCustomRHS (custom x) = refl
    fromToRepOpenCustomRHS (sub x) = refl

    toFromRepOpenCustomRHS : ∀ {m} (rocrhs : RepOpenCustomRHS m) → toRepOpenCustomRHS (fromRepOpenCustomRHS rocrhs) ≡ rocrhs
    toFromRepOpenCustomRHS (inl x) = refl
    toFromRepOpenCustomRHS (inr x) = refl

    isoRepOpenCustomRHS : ∀ {m} → OpenCustomRHS m ≅ RepOpenCustomRHS m
    fun isoRepOpenCustomRHS = toRepOpenCustomRHS
    inv isoRepOpenCustomRHS = fromRepOpenCustomRHS
    rightInv isoRepOpenCustomRHS = toFromRepOpenCustomRHS
    leftInv isoRepOpenCustomRHS = fromToRepOpenCustomRHS

    isGroupoidRepOpenCustomRHS : ∀ {m} → isGroupoid (RepOpenCustomRHS m)
    isGroupoidRepOpenCustomRHS = isOfHLevel⊎ 1 (isGroupoidCustomRHS cmatsig) (isSet→isGroupoid (isSetCtx cmatsig))

  isGroupoidOpenCustomRHS : ∀ {m} → isGroupoid (OpenCustomRHS m)
  isGroupoidOpenCustomRHS = isOfHLevelRetractFromIso 3 isoRepOpenCustomRHS isGroupoidRepOpenCustomRHS

  {- The signature of the open translation.
  -}
  cmatsigOpen : Mode cmatsig → CmatSignature
  catModeJunctor (cmatsigOpen m) = catModeJunctor cmatsig
  pshCtx (cmatsigOpen m) =
    funcComp (HomFunctor (catModeJunctor cmatsig)) (rinj (catModeJunctor cmatsig ^op) (catModeJunctor cmatsig) m)
  isGroupoidMode (cmatsigOpen m) = isGroupoidMode cmatsig
  CustomRHS (cmatsigOpen m) = OpenCustomRHS
  isGroupoidCustomRHS (cmatsigOpen m) = isGroupoidOpenCustomRHS

  rhsOrig→Open : ∀ {m0 m : Mode cmatsig} → RHS cmatsig m → RHS (cmatsigOpen m0) m
  rhsOrig→Open (custom crhs) = custom (custom crhs)
  rhsOrig→Open (sub Γ) = custom (sub Γ)
  rhsOrig→Open (jhom Ψ Φ) = jhom Ψ Φ

  arityOrig→Open : ∀ {m0 m : Mode cmatsig} → CArity cmatsig m → CArity (cmatsigOpen m0) m
  arityOrig→Open [] = []
  arityOrig→Open ((n , Φ , rhs) ∷ arity) = (n , Φ , rhsOrig→Open rhs) ∷ arityOrig→Open arity
