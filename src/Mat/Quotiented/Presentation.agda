{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monad.Base

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term

module Mat.Quotiented.Presentation where

module EqTheory {sign : Signature} (presF : PresentationF sign) where
  open Signature sign
  open PresentationF presF
  open Mat.Free.Term presF
  open Category hiding (_∘_)
  open Functor
  open IsMonad
  open NatTrans
  
  record EqTheory : Type where

    field
      Axiom : Sort → Type
      isSetAxiom : {sortOut : Sort} → isSet (Axiom sortOut)
      msetArity : ∀ {sortOut} → Axiom sortOut → MSet
      lhs rhs : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → TermF (mtyp (msetArity axiom)) sortOut

  module _ (eqTheory : EqTheory) where
    open EqTheory eqTheory public

    data Term (X : MType) : (sort : Sort) → Type where
      var : ∀ {sortOut} → X sortOut → Term X sortOut
      ast : ∀ {sortOut} → Term1 (Term X) sortOut → Term X sortOut
      joinFQ : ∀ {sortOut} → TermF (Term X) sortOut → Term X sortOut
      joinFQ-varF : ∀ {sortOut} → (t : Term X sortOut) → joinFQ (varF t) ≡ t
      joinFQ-astF : ∀ {sortOut} → (t : Term1 (TermF (Term X)) sortOut)
        → joinFQ (astF t) ≡ ast (mapTerm1 (λ sort → joinFQ) sortOut t)
      byAxiom : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → Term X sort)
        → joinFQ (mapTermF f sortOut (lhs axiom))
        ≡ joinFQ (mapTermF f sortOut (rhs axiom))
      isSetTerm : ∀ {sortOut} → isSet (Term X sortOut)

    pureTerm : {X : MType} → (sort : Sort) → X sort → Term X sort
    pureTerm sort x = var x

    {-# TERMINATING #-}
    joinTerm : {X : MType} → (sort : Sort) → Term (Term X) sort → Term X sort
    joinTerm sort (var t) = t
    joinTerm sort (ast t) = ast (mapTerm1 joinTerm sort t)
    joinTerm sort (joinFQ t) = joinFQ (mapTermF joinTerm sort t)
    joinTerm sort (joinFQ-varF t i) = joinFQ-varF (joinTerm sort t) i
    joinTerm sort (joinFQ-astF t i) = joinFQ-astF (mapTerm1 (mapTermF joinTerm) sort t) i
    joinTerm sort (byAxiom axiom f i) = hcomp
      (λ where
         j (i = i0) → joinFQ (mapTermF-∘ joinTerm f j sort (lhs axiom))
         j (i = i1) → joinFQ (mapTermF-∘ joinTerm f j sort (rhs axiom))
      )
      (byAxiom axiom (λ sort' y → joinTerm sort' (f sort' y)) i)
    joinTerm sort (isSetTerm t1 t2 et et' i j) = isSetTerm
      (joinTerm sort t1)
      (joinTerm sort t2)
      (λ k → joinTerm sort (et k))
      (λ k → joinTerm sort (et' k)) i j

    msetTerm : MSet → MSet
    fst (msetTerm msetX sortOut) = Term (mtyp msetX) sortOut
    snd (msetTerm msetX sortOut) = isSetTerm

    {-# TERMINATING #-}
    mapTerm : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → Term X sort → Term Y sort
    mapTerm f sort (var x) = var (f sort x)
    mapTerm f sort (ast t) = ast (mapTerm1 (mapTerm f) sort t)
    mapTerm f sort (joinFQ t) = joinFQ (mapTermF (mapTerm f) sort t)
    mapTerm f sort (joinFQ-varF t i) = joinFQ-varF (mapTerm f sort t) i
    mapTerm f sort (joinFQ-astF t i) = joinFQ-astF (mapTerm1 (mapTermF (mapTerm f)) sort t) i
    mapTerm f sort (byAxiom axiom g i) = hcomp
      (λ where
        j (i = i0) → joinFQ (mapTermF-∘ (mapTerm f) g j sort (lhs axiom))
        j (i = i1) → joinFQ (mapTermF-∘ (mapTerm f) g j sort (rhs axiom))
      )
      (byAxiom axiom (λ sort' y → mapTerm f sort' (g sort' y)) i)
    mapTerm f sort (isSetTerm t1 t2 et et' i j) = isSetTerm
      (mapTerm f sort t1)
      (mapTerm f sort t2)
      (λ k → mapTerm f sort (et k))
      (λ k → mapTerm f sort (et' k)) i j

    {-# TERMINATING #-}
    mapTerm-id : ∀ {X} → mapTerm (λ sort → idfun (X sort)) ≡ (λ sort → idfun (Term X sort))
    mapTermF-mapTerm-id : ∀ {X} → mapTermF (mapTerm (λ sort → idfun (X sort))) ≡ (λ sort → idfun (TermF (Term X) sort))
    mapTerm-id i sort (var x) = var x
    mapTerm-id i sort (ast t) = ast (mapTerm1 (mapTerm-id i) sort t)
    mapTerm-id i sort (joinFQ t) = joinFQ (mapTermF-mapTerm-id i sort t)
    mapTerm-id {X = X} i sort (joinFQ-varF t j) = --{!joinFQ-varF (mapTerm-id i sort t) j!}
      idfun
        (Square
          (λ j → joinFQ-varF (mapTerm (λ sort₁ → idfun (X sort₁)) sort t) j)
          (λ j → idfun (Term X sort) (joinFQ-varF t j))
          (λ i → joinFQ (mapTermF-mapTerm-id i sort (varF t)))
          (λ i → mapTerm-id i sort t)
        ) (toPathP (isSetTerm _ _ _ _)) i j
    mapTerm-id i sort (joinFQ-astF (term1 o args) j) =
      idfun
        (Square
          (λ j → joinFQ-astF (term1 o (λ p → mapTermF (mapTerm (λ sort₁ x → x)) (arity o ! p) (args p))) j)
          (λ j → joinFQ-astF (term1 o args) j)
          (λ i →  joinFQ (mapTermF-mapTerm-id i sort (astF (term1 o args)))
          )
          (λ i →  ast (term1 o λ p → joinFQ (mapTermF-mapTerm-id i (arity o ! p) (args p)))
          )
        ) (toPathP (isSetTerm _ _ _ _)) i j
    mapTerm-id {X = X} k sort (byAxiom axiom f i) =
      idfun
        (Square
          (λ i → mapTerm (λ _ x → x) sort (byAxiom axiom f i))
          (λ i → byAxiom axiom f i)
          (λ k → joinFQ (mapTermF-mapTerm-id k sort (mapTermF f sort (lhs axiom))))
          λ k → joinFQ (mapTermF-mapTerm-id k sort (mapTermF f sort (rhs axiom)))
        ) (toPathP (isSetTerm _ _ _ _)) k i
    mapTerm-id i sort (isSetTerm t1 t2 et et' j k) = isSetTerm
      (mapTerm-id i sort t1)
      (mapTerm-id i sort t2)
      (λ k → mapTerm-id i sort (et k))
      (λ k → mapTerm-id i sort (et' k)) j k
    mapTermF-mapTerm-id i = idfun (mapTermF (mapTerm (λ sort₁ x₁ → x₁)) ≡ (λ _ t → t))
      (cong mapTermF mapTerm-id ∙ mapTermF-id)
      i

    {-# TERMINATING #-}
    mapTerm-∘ : ∀ {X Y Z : MType}
      → (g : ∀ sort → Y sort → Z sort)
      → (f : ∀ sort → X sort → Y sort)
      → mapTerm (λ sort → g sort ∘ f sort) ≡ (λ sort → mapTerm g sort ∘ mapTerm f sort)
    mapTermF-mapTerm-∘ : ∀ {X Y Z : MType}
      → (g : ∀ sort → Y sort → Z sort)
      → (f : ∀ sort → X sort → Y sort)
      → mapTermF (mapTerm (λ sort → g sort ∘ f sort)) ≡ (λ sort → mapTermF (mapTerm g) sort ∘ mapTermF (mapTerm f) sort)
    mapTerm-∘ g f i sort (var x) = var (g sort (f sort x))
    mapTerm-∘ g f i sort (ast t) = ast (mapTerm1 (mapTerm-∘ g f i) sort t)
    mapTerm-∘ g f i sort (joinFQ t) = joinFQ (mapTermF-mapTerm-∘ g f i sort t)
    mapTerm-∘ g f i sort (joinFQ-varF t j) =
      idfun
        (Square
          (λ j → joinFQ-varF (mapTerm (λ sort₁ → g sort₁ ∘ f sort₁) sort t) j)
          (λ j → (mapTerm g sort ∘ mapTerm f sort) (joinFQ-varF t j))
          (λ i → joinFQ (mapTermF-mapTerm-∘ g f i sort (varF t)))
          λ i → mapTerm-∘ g f i sort t
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    mapTerm-∘ g f i sort (joinFQ-astF (term1 o args) j) =
      idfun
        (Square
          (λ j → joinFQ-astF (term1 o (λ p →
            mapTermF (mapTerm (λ sort₁ x → g sort₁ (f sort₁ x))) (arity o ! p) (args p))) j)
          (λ j → joinFQ-astF (term1 o (λ p →
            mapTermF (mapTerm g) (arity o ! p) (mapTermF (mapTerm f) (arity o ! p) (args p)))) j)
          (λ i → joinFQ (mapTermF-mapTerm-∘ g f i sort (astF (term1 o args))))
          (λ i → ast (term1 o λ p → joinFQ (mapTermF-mapTerm-∘ g f i (arity o ! p) (args p))))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    mapTerm-∘ g f k sort (byAxiom axiom h i) =
      idfun
        (Square
          (λ i → mapTerm (λ sort₁ → g sort₁ ∘ f sort₁) sort (byAxiom axiom h i))
          (λ i → (mapTerm g sort ∘ mapTerm f sort) (byAxiom axiom h i))
          (λ k → joinFQ (mapTermF-mapTerm-∘ g f k sort (mapTermF h sort (lhs axiom))))
          (λ k → joinFQ (mapTermF-mapTerm-∘ g f k sort (mapTermF h sort (rhs axiom))))
        ) (toPathP (isSetTerm _ _ _ _)) k i
    mapTerm-∘ g f i sort (isSetTerm t1 t2 et et' j k) = isSetTerm
      (mapTerm-∘ g f i sort t1)
      (mapTerm-∘ g f i sort t2)
      (λ k → mapTerm-∘ g f i sort (et k))
      (λ k → mapTerm-∘ g f i sort (et' k)) j k
    mapTermF-mapTerm-∘ g f = cong mapTermF (mapTerm-∘ g f) ∙ mapTermF-∘ (mapTerm g) (mapTerm f)

    {-# TERMINATING #-}
    joinTerm-nat : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort) →
      (λ sort → joinTerm sort ∘ mapTerm (mapTerm f) sort)
      ≡ (λ sort → mapTerm f sort ∘ joinTerm sort)
    mapTermF-joinTerm-nat : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort) →
      (λ sort → mapTermF joinTerm sort ∘ mapTermF (mapTerm (mapTerm f)) sort)
      ≡ (λ sort → mapTermF (mapTerm f) sort ∘ mapTermF joinTerm sort)
    joinTerm-nat f i sort (var t) = mapTerm f sort t
    joinTerm-nat f i sort (ast t) = ast (mapTerm1 (joinTerm-nat f i) sort t)
    joinTerm-nat f i sort (joinFQ t) = joinFQ (mapTermF-joinTerm-nat f i sort t)
    joinTerm-nat f i sort (joinFQ-varF t j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm (mapTerm f) sort) (joinFQ-varF t j))
          (λ j → (mapTerm f sort ∘ joinTerm sort) (joinFQ-varF t j))
          (λ i → joinFQ (mapTermF-joinTerm-nat f i sort (varF t)))
          (λ i → joinTerm-nat f i sort t)
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-nat f i sort (joinFQ-astF t@(term1 o args) j) =
      idfun
        (Square
          (λ j → joinFQ-astF (mapTerm1 (mapTermF joinTerm) sort
            (mapTerm1 (mapTermF (mapTerm (mapTerm f))) sort (term1 o args))) j)
          (λ j → joinFQ-astF (mapTerm1 (mapTermF (mapTerm f)) sort
            (mapTerm1 (mapTermF joinTerm) sort (term1 o args))) j)
          (λ i → joinFQ (mapTermF-joinTerm-nat f i sort (astF t)))
          (λ i → ast (mapTerm1 (joinTerm-nat f i) sort (mapTerm1 (λ sort₁ → joinFQ) sort t)))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-nat f i sort (byAxiom axiom g j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm (mapTerm f) sort) (byAxiom axiom g j))
          (λ j → (mapTerm f sort ∘ joinTerm sort) (byAxiom axiom g j))
          (λ i → joinFQ (mapTermF-joinTerm-nat f i sort (mapTermF g sort (lhs axiom))))
          (λ i → joinFQ (mapTermF-joinTerm-nat f i sort (mapTermF g sort (rhs axiom))))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-nat f i sort (isSetTerm t1 t2 et et' j k) = isSetTerm
      (joinTerm-nat f i sort t1)
      (joinTerm-nat f i sort t2)
      (λ k → joinTerm-nat f i sort (et k))
      (λ k → joinTerm-nat f i sort (et' k)) j k
    mapTermF-joinTerm-nat f =
      (λ sort → mapTermF joinTerm sort ∘ mapTermF (mapTerm (mapTerm f)) sort)
        ≡⟨ sym (mapTermF-∘ joinTerm (mapTerm (mapTerm f))) ⟩
      mapTermF (λ sort → joinTerm sort ∘ mapTerm (mapTerm f) sort)
        ≡⟨ cong mapTermF (joinTerm-nat f) ⟩
      mapTermF (λ sort → mapTerm f sort ∘ joinTerm sort)
        ≡⟨ mapTermF-∘ (mapTerm f) joinTerm ⟩
      (λ sort → mapTermF (mapTerm f) sort ∘ mapTermF joinTerm sort) ∎

    {-# TERMINATING #-}
    joinTerm-lUnit : ∀ {X : MType} →
      (λ sort → joinTerm sort ∘ mapTerm pureTerm sort) ≡ λ (sort : Sort) → idfun (Term X sort)
    mapTermF-joinTerm-lUnit : ∀ {X : MType} →
      (λ sort → mapTermF joinTerm sort ∘ mapTermF (mapTerm pureTerm) sort) ≡ λ (sort : Sort) → idfun (TermF (Term X) sort)
    joinTerm-lUnit i sort (var x) = var x
    joinTerm-lUnit i sort (ast t) = ast (mapTerm1 (joinTerm-lUnit i) sort t)
    joinTerm-lUnit i sort (joinFQ t) = joinFQ (mapTermF-joinTerm-lUnit i sort t)
    joinTerm-lUnit i sort (joinFQ-varF t j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm pureTerm sort) (joinFQ-varF t j))
          (λ j → joinFQ-varF t j)
          (λ i → joinFQ (varF (joinTerm-lUnit i sort t)))
          (λ i → joinTerm-lUnit i sort t)
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-lUnit i sort (joinFQ-astF t j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm pureTerm sort) (joinFQ-astF t j))
          (λ j → joinFQ-astF t j)
          (λ i → joinFQ (astF (mapTerm1 (mapTermF-joinTerm-lUnit i) sort t)))
          (λ i → ast (mapTerm1 (joinTerm-lUnit i) sort (mapTerm1 (λ sort₁ → joinFQ) sort t)))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-lUnit i sort (byAxiom axiom f j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm pureTerm sort) (byAxiom axiom f j))
          (λ j → byAxiom axiom f j)
          (λ i → joinFQ (mapTermF-joinTerm-lUnit i sort (mapTermF f sort (lhs axiom))))
          (λ i → joinFQ (mapTermF-joinTerm-lUnit i sort (mapTermF f sort (rhs axiom))))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-lUnit i sort (isSetTerm t1 t2 et et' j k) = isSetTerm
      (joinTerm-lUnit i sort t1)
      (joinTerm-lUnit i sort t2)
      (λ j → joinTerm-lUnit i sort (et j))
      (λ j → joinTerm-lUnit i sort (et' j)) j k
    mapTermF-joinTerm-lUnit i sort (varF t) = varF (joinTerm-lUnit i sort t)
    mapTermF-joinTerm-lUnit i sort (astF t) = astF (mapTerm1 (mapTermF-joinTerm-lUnit i) sort t)

    {-# TERMINATING #-}
    joinTerm-assoc : ∀ {X : MType} →
      (λ (sort : Sort) → joinTerm {X = X} sort ∘ mapTerm joinTerm sort) ≡ (λ sort → joinTerm sort ∘ joinTerm sort)
    mapTermF-joinTerm-assoc : ∀ {X : MType} →
      (λ (sort : Sort) → mapTermF (joinTerm {X = X}) sort ∘ mapTermF (mapTerm joinTerm) sort)
      ≡ (λ sort → mapTermF joinTerm sort ∘ mapTermF joinTerm sort)
    joinTerm-assoc i sort (var t) = joinTerm sort t
    joinTerm-assoc i sort (ast t) = ast (mapTerm1 (joinTerm-assoc i) sort t)
    joinTerm-assoc i sort (joinFQ t) = joinFQ (mapTermF-joinTerm-assoc i sort t)
    joinTerm-assoc i sort (joinFQ-varF t j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm joinTerm sort) (joinFQ-varF t j))
          (λ j → (joinTerm sort ∘ joinTerm sort) (joinFQ-varF t j))
          (λ i → joinFQ (varF (joinTerm-assoc i sort t)))
          (λ i → joinTerm-assoc i sort t)
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-assoc i sort (joinFQ-astF t j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm joinTerm sort) (joinFQ-astF t j))
          (λ j → (joinTerm sort ∘ joinTerm sort) (joinFQ-astF t j))
          (λ i → joinFQ (astF (mapTerm1 (mapTermF-joinTerm-assoc i) sort t)))
          (λ i → ast (mapTerm1 (joinTerm-assoc i) sort (mapTerm1 (λ sort₁ → joinFQ) sort t)))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-assoc i sort (byAxiom axiom f j) =
      idfun
        (Square
          (λ j → (joinTerm sort ∘ mapTerm joinTerm sort) (byAxiom axiom f j))
          (λ j → (joinTerm sort ∘ joinTerm sort) (byAxiom axiom f j))
          (λ i → joinFQ (mapTermF-joinTerm-assoc i sort (mapTermF f sort (lhs axiom))))
          (λ i → joinFQ (mapTermF-joinTerm-assoc i sort (mapTermF f sort (rhs axiom))))
        )
        (toPathP (isSetTerm _ _ _ _)) i j
    joinTerm-assoc i sort (isSetTerm t1 t2 et et' j k) = isSetTerm
      (joinTerm-assoc i sort t1)
      (joinTerm-assoc i sort t2)
      (λ j → joinTerm-assoc i sort (et j))
      (λ j → joinTerm-assoc i sort (et' j)) j k
    mapTermF-joinTerm-assoc i sort (varF t) = varF (joinTerm-assoc i sort t)
    mapTermF-joinTerm-assoc i sort (astF t) = astF (mapTerm1 (mapTermF-joinTerm-assoc i) sort t)

    ftrTerm : Functor catMSet catMSet
    F-ob ftrTerm = msetTerm
    F-hom ftrTerm = mapTerm
    F-id ftrTerm = mapTerm-id
    F-seq ftrTerm f g = mapTerm-∘ g f

    ismonadTerm : IsMonad ftrTerm
    N-ob (η ismonadTerm) msetX sort = var
    N-hom (η ismonadTerm) f = refl
    N-ob (μ ismonadTerm) msetX = joinTerm
    N-hom (μ ismonadTerm) {msetX}{msetY} f = joinTerm-nat f
    idl-μ ismonadTerm = makeNatTransPathP F-rUnit (λ i → ftrTerm) refl
    idr-μ ismonadTerm = makeNatTransPathP F-lUnit (λ i → ftrTerm) (funExt λ msetX → joinTerm-lUnit)
    assoc-μ ismonadTerm = makeNatTransPathP F-assoc (λ i → ftrTerm) (funExt λ msetX → joinTerm-assoc)

    monadTerm : Monad catMSet
    monadTerm = ftrTerm , ismonadTerm

EqTheory = EqTheory.EqTheory

record Presentation (sign : Signature) : Type where
  constructor presentation
  field
    getPresentationF : PresentationF sign
    getEqTheory : EqTheory getPresentationF
