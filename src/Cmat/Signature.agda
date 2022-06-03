{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.FinData
open import Cubical.Data.FinData
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

  CanBeClosed : Type
  CanBeClosed = Terminal catModeJunctor

  PshCtx : Type
  PshCtx = Functor catModeJunctor (SET _)

  record CmatFoundation : Type where
    constructor cmatfndClosed
    field
      pshCtx : PshCtx

    Ctx : Mode → Type
    Ctx m = fst (F-ob pshCtx m)

    isSetCtx : isSet (Ctx m)
    isSetCtx {m} = snd (F-ob pshCtx m)

    _:⦊_ : Ctx m → Junctor m n → Ctx n
    Γ :⦊ Ψ = F-hom pshCtx Ψ Γ

    record Jud : Type where
      eta-equality
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
      isGroupoidRepJud = isOfHLevelΣ 3 isGroupoidMode λ m →
                         isOfHLevelΣ 3 (isSet→isGroupoid isSetCtx) (λ _ → isGroupoidRHS)

    isGroupoidJud : isGroupoid Jud
    isGroupoidJud = isOfHLevelRetractFromIso 3 isoRepJud isGroupoidRepJud

    {-
    -- contextual arity
    CArity' : (Mode → Type) → Mode → Type
    CArity' X m = List (Σ[ n ∈ Mode ] Junctor m n × RHS' X n)

    mapCArity' : ∀ {X Y : Mode → Type} → (f : ∀ m → X m → Y m) → CArity' X m → CArity' Y m
    mapCArity' f = map (λ (n , Φ , rhs) → n , Φ , mapRHS' f rhs)
    -}

  open CmatFoundation.Jud public

  module _ (m0 : Mode) where

    pshYoneda : PshCtx
    pshYoneda = funcComp (HomFunctor catModeJunctor) (rinj _ _ m0)

    cmatfndOpen : CmatFoundation
    cmatfndOpen = cmatfndClosed pshYoneda

    open CmatFoundation cmatfndOpen

    JudOpen : Type
    JudOpen = Jud

    CArity : Type
    CArity = List JudOpen

    isGroupoidCArity : isGroupoid CArity
    isGroupoidCArity = isOfHLevelList 1 isGroupoidJud

  module _ (cmatfnd : CmatFoundation) where
    open MatSignature
    open CmatFoundation cmatfnd

    {- The signature of the MAT translation.
    -}
    matsigClosed : MatSignature
    Sort matsigClosed = Jud
    isGroupoidSort matsigClosed = isGroupoidJud

    arityClosed : (Γ : Ctx m) → CArity m → Arity matsigClosed
    arityClosed Γ = map (λ (Φ ⊩ rhs) → (Γ :⦊ Φ ⊩ rhs))

    length-arityClosed : ∀ {m} (Γ : Ctx m) → (arity : CArity m)
      → length (arityClosed Γ arity) ≡ length arity
    length-arityClosed Γ = length-map _

    lookup-arityClosed : ∀ {m} (Γ : Ctx m) → (arity : CArity m)
      → (p0 : Fin (length (arityClosed Γ arity)))
      → (p1 : Fin (length arity))
      → (p : PathP (λ i → Fin (length-arityClosed Γ arity i)) p0 p1)
      → lookup (arityClosed Γ arity) p0
       ≡ ((Γ :⦊ jud'ctx (lookup arity p1)) ⊩ jud'rhs (lookup arity p1))
    lookup-arityClosed Γ = lookup-map _

  module _ (m0 : Mode) where

    matsigOpen = matsigClosed (cmatfndOpen m0)

    arityOpen = arityClosed (cmatfndOpen m0)

    length-arityOpen = length-arityClosed (cmatfndOpen m0)

    lookup-arityOpen = lookup-arityClosed (cmatfndOpen m0)
