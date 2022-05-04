{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term

module Mat.Quotiented.Presentation where

module EqTheory {sign : Signature} (presF : PresentationF sign) where
  open Signature sign
  open PresentationF presF
  open Mat.Free.Term presF
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
      astQ : ∀ {sortOut} → TermF (Term X) sortOut → Term X sortOut
      astQ-varF : ∀ {sortOut} → (t : Term X sortOut) → astQ (varF t) ≡ t
      astQ-astF : ∀ {sortOut} → (t : Term1 (TermF (Term X)) sortOut)
        → astQ (astF t) ≡ ast (mapTerm1 (λ sort → astQ) sortOut t)
      byAxiom : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → Term X sort)
        → astQ (mapTermF f sortOut (lhs axiom))
        ≡ astQ (mapTermF f sortOut (rhs axiom))
      isSetTerm : ∀ {sortOut} → isSet (Term X sortOut)

    joinTerm : {X : MType} → (sort : Sort) → Term (Term X) sort → Term X sort
    mapTermF-joinTerm : {X : MType} → (sort : Sort) → TermF (Term (Term X)) sort → TermF (Term X) sort
    mapTerm1-mapTermF-joinTerm : {X : MType} → (sort : Sort) → Term1 (TermF (Term (Term X))) sort
      → Term1 (TermF (Term X)) sort
    mapTermF-joinTerm-∘ : {X Y : MType}
      → (f : ∀ sort → Y sort → Term (Term X) sort)
      → (sort : Sort) → (t : TermF Y sort)
      → mapTermF (λ sort' → joinTerm sort' ∘ f sort') sort t ≡ mapTermF-joinTerm sort (mapTermF f sort t)

    joinTerm sort (var t) = t
    joinTerm sort (ast (term1 o args)) = ast (term1 o λ p → joinTerm (arity o ! p) (args p))
    joinTerm sort (astQ t) = astQ (mapTermF-joinTerm sort t)
    joinTerm sort (astQ-varF t i) = astQ-varF (joinTerm sort t) i
    joinTerm sort (astQ-astF t i) = astQ-astF (mapTerm1-mapTermF-joinTerm sort t) i
    joinTerm sort (byAxiom axiom f i) = hcomp
      (λ where
         j (i = i0) → astQ (mapTermF-joinTerm-∘ f sort (lhs axiom) j)
         j (i = i1) → astQ (mapTermF-joinTerm-∘ f sort (rhs axiom) j)
      )
      (byAxiom axiom (λ sort' y → joinTerm sort' (f sort' y)) i)
    joinTerm sort (isSetTerm t1 t2 et et' i j) = isSetTerm
      (joinTerm sort t1)
      (joinTerm sort t2)
      (λ k → joinTerm sort (et k))
      (λ k → joinTerm sort (et' k)) i j
    mapTermF-joinTerm sort (varF t) = varF (joinTerm sort t)
    mapTermF-joinTerm sort (astF t) = astF (mapTerm1-mapTermF-joinTerm sort t)
    mapTerm1-mapTermF-joinTerm sort (term1 o args) = term1 o λ p → mapTermF-joinTerm (arity o ! p) (args p)
    mapTermF-joinTerm-∘ f sort (varF y) i = varF (joinTerm sort (f sort y))
    mapTermF-joinTerm-∘ f sort (astF (term1 o args)) i =
      astF (term1 o λ p → mapTermF-joinTerm-∘ f (arity o ! p) (args p) i)

    msetTerm : MSet → MSet
    fst (msetTerm msetX sortOut) = Term (mtyp msetX) sortOut
    snd (msetTerm msetX sortOut) = isSetTerm

    mapTerm : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → Term X sort → Term Y sort
    mapTermF-mapTerm : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → TermF (Term X) sort → TermF (Term Y) sort
    mapTermF-mapTerm-∘ : {Z X Y : MType} → (f : ∀ sort → X sort → Y sort) 
      → (g : ∀ sort → Z sort → Term X sort)
      → (sort : Sort) → (t : TermF Z sort)
      → mapTermF (λ sort' → mapTerm f sort' ∘ g sort') sort t ≡ mapTermF-mapTerm f sort (mapTermF g sort t)

    mapTerm f sort (var x) = var (f sort x)
    mapTerm f sort (ast (term1 o args)) = ast (term1 o λ p → mapTerm f (arity o ! p) (args p))
    mapTerm f sort (astQ t) = astQ (mapTermF-mapTerm f sort t)
    mapTerm f sort (astQ-varF t i) = astQ-varF (mapTerm f sort t) i
    mapTerm f sort (astQ-astF (term1 o args) i) = astQ-astF (term1 o λ p → mapTermF-mapTerm f (arity o ! p) (args p)) i
    mapTerm f sort (byAxiom axiom g i) = hcomp
      (λ where
        j (i = i0) → astQ (mapTermF-mapTerm-∘ f g sort (lhs axiom) j)
        j (i = i1) → astQ (mapTermF-mapTerm-∘ f g sort (rhs axiom) j)
      )
      (byAxiom axiom (λ sort' y → mapTerm f sort' (g sort' y)) i)
    mapTerm f sort (isSetTerm t1 t2 et et' i j) = isSetTerm
      (mapTerm f sort t1)
      (mapTerm f sort t2)
      (λ k → mapTerm f sort (et k))
      (λ k → mapTerm f sort (et' k)) i j
    mapTermF-mapTerm f sort (varF t) = varF (mapTerm f sort t)
    mapTermF-mapTerm f sort (astF (term1 o args)) = astF (term1 o λ p → mapTermF-mapTerm f (arity o ! p) (args p))
    mapTermF-mapTerm-∘ f g sort (varF x) i = varF (mapTerm f sort (g sort x))
    mapTermF-mapTerm-∘ f g sort (astF (term1 o args)) i = astF (term1 o λ p → mapTermF-mapTerm-∘ f g (arity o ! p) (args p) i)

    mapTerm-byAxiom : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort) → ∀ sortOut
      → (axiom : Axiom sortOut) → (g : ∀ sort → mtyp (msetArity axiom) sort → Term X sort)
      → PathP
           (λ j → astQ (mapTermF-mapTerm-∘ f g sortOut (lhs axiom) j)
                 ≡ astQ (mapTermF-mapTerm-∘ f g sortOut (rhs axiom) j)
           )
           (λ i → byAxiom axiom (λ sort y → mapTerm f sort (g sort y)) i)
           (λ i → mapTerm f sortOut (byAxiom axiom g i))
    mapTerm-byAxiom f sortOut axiom g = toPathP (isSetTerm _ _ _ _)

    {-# TERMINATING #-}
    mapTerm-id : ∀ {X} → mapTerm (λ sort → idfun (X sort)) ≡ (λ sort → idfun (Term X sort))
    mapTermF-mapTerm-id : ∀ {X} → mapTermF-mapTerm (λ sort → idfun (X sort)) ≡ (λ sort → idfun (TermF (Term X) sort))
    mapTermF-mapTerm-id-∘ : ∀ {Z X : MType}
      → (g : ∀ sort → Z sort → Term X sort)
      → (sort : Sort) → (t : TermF Z sort)
      → PathP
           (λ j → idfun
                     ( mapTermF (λ sort' x → mapTerm (λ sort₁ x₁ → x₁) sort' (g sort' x)) sort t
                     ≡ mapTermF-mapTerm (λ sort₁ x → x) sort (mapTermF g sort t)
                     )
                     (mapTermF-mapTerm-∘ (λ sort₁ x → x) g sort t) j
                 ≡ idfun
                     ( mapTermF g sort t
                     ≡ mapTermF g sort t
                     )
                     refl j
           )
           (λ i → mapTermF (λ sort' → mapTerm-id i sort' ∘ g sort') sort t)
           (λ i → mapTermF-mapTerm-id i sort (mapTermF g sort t))
    mapTerm-id i sort (var x) = var x
    mapTerm-id i sort (ast (term1 o args)) = ast (term1 o λ p → mapTerm-id i (arity o ! p) (args p))
    mapTerm-id i sort (astQ t) = astQ (mapTermF-mapTerm-id i sort t)
    mapTerm-id i sort (astQ-varF t j) = astQ-varF (mapTerm-id i sort t) j
    mapTerm-id i sort (astQ-astF (term1 o args) j) = astQ-astF (term1 o λ p → mapTermF-mapTerm-id i (arity o ! p) (args p)) j
    mapTerm-id {X = X} k sort (byAxiom axiom f i) = hcomp
      (λ where
        j (i = i0) → astQ (mapTermF-mapTerm-id-∘ f sort (lhs axiom) j k)
        j (i = i1) → astQ (mapTermF-mapTerm-id-∘ f sort (rhs axiom) j k)
        j (k = i0) → idfun
          ( byAxiom axiom (λ sort' y → mapTerm (λ sort₁ x → x) sort' (f sort' y)) i
          ≡ mapTerm (λ sort → idfun (X sort)) sort (byAxiom axiom f i)
          )
          (λ k' → mapTerm-byAxiom (λ _ x → x) sort axiom f k' i) j
        j (k = i1) → idfun
          ( byAxiom axiom f i
          ≡ byAxiom axiom f i
          )
          refl j
      )
      (byAxiom axiom (λ sort' y → mapTerm-id k sort' (f sort' y)) i)
    mapTerm-id i sort (isSetTerm t1 t2 et et' j k) = isSetTerm
      (mapTerm-id i sort t1)
      (mapTerm-id i sort t2)
      (λ k → mapTerm-id i sort (et k))
      (λ k → mapTerm-id i sort (et' k)) j k
    mapTermF-mapTerm-id i sort (varF t) = varF (mapTerm-id i sort t)
    mapTermF-mapTerm-id i sort (astF (term1 o args)) = astF (term1 o λ p → mapTermF-mapTerm-id i (arity o ! p) (args p))
    mapTermF-mapTerm-id-∘ g sort t =
      toPathP (isSetTermF (λ z → Term _ z , isSetTerm) sort _ _ _ _)

EqTheory = EqTheory.EqTheory

record Presentation (sign : Signature) : Type where
  constructor presentationQ
  field
    getPresentationF : PresentationF sign
    getEqTheory : EqTheory getPresentationF
