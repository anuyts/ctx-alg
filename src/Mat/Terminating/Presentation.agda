{-# OPTIONS --cubical --type-in-type #-}

{- This file is not in use, and attempts to use the workaround desribed by Fiore & Szamozvancev (2022)
to convince Agda of termination of eliminators without using sized types. I decided this workaround
was becoming too frustrating, so now I just use a TERMINATING pragma. -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.TermQ

module Mat.TermQinating.Presentation where

module EqTheory {sign : Signature} (presF : PresentationF sign) where
  open Signature sign
  open PresentationF presF
  open Mat.Free.TermQ presF
  record EqTheory : Type where

    field
      Axiom : Sort → Type
      isSetAxiom : {sortOut : Sort} → isSet (Axiom sortOut)
      msetArity : ∀ {sortOut} → Axiom sortOut → MSet
      lhs rhs : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → TermF (mtyp (msetArity axiom)) sortOut

  module _ (eqTheory : EqTheory) where
    open EqTheory eqTheory public

    data TermQ (X : MType) : (sort : Sort) → Type where
      varQ : ∀ {sortOut} → X sortOut → TermQ X sortOut
      join1Q : ∀ {sortOut} → Term1 (TermQ X) sortOut → TermQ X sortOut
      join1Q : ∀ {sortOut} → TermF (TermQ X) sortOut → TermQ X sortOut
      join1Q-varF : ∀ {sortOut} → (t : TermQ X sortOut) → join1Q (varF t) ≡ t
      join1Q-join1F : ∀ {sortOut} → (t : Term1 (TermF (TermQ X)) sortOut)
        → join1Q (join1F t) ≡ join1Q (mapTerm1 (λ sort → join1Q) sortOut t)
      byAxiom : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → TermQ X sort)
        → join1Q (mapTermF f sortOut (lhs axiom))
        ≡ join1Q (mapTermF f sortOut (rhs axiom))
      isSetTermQ : ∀ {sortOut} → isSet (TermQ X sortOut)

    joinTermQ : {X : MType} → (sort : Sort) → TermQ (TermQ X) sort → TermQ X sort
    -- The following lemmas are needed because we don't use sized types.
    mapTermF-joinTermQ : {X : MType} → (sort : Sort) → TermF (TermQ (TermQ X)) sort → TermF (TermQ X) sort
    mapTerm1-mapTermF-joinTermQ : {X : MType} → (sort : Sort) → Term1 (TermF (TermQ (TermQ X))) sort
      → Term1 (TermF (TermQ X)) sort
    mapTermF-joinTermQ-∘' : {X Y : MType}
      → (f : ∀ sort → Y sort → TermQ (TermQ X) sort)
      → (sort : Sort) → (t : TermF Y sort)
      → mapTermF (λ sort' → joinTermQ sort' ∘ f sort') sort t ≡ mapTermF-joinTermQ sort (mapTermF f sort t)

    joinTermQ sort (varQ t) = t
    joinTermQ sort (join1Q (term1 o args)) = join1Q (term1 o λ p → joinTermQ (arity o ! p) (args p))
    joinTermQ sort (join1Q t) = join1Q (mapTermF-joinTermQ sort t)
    joinTermQ sort (join1Q-varF t i) = join1Q-varF (joinTermQ sort t) i
    joinTermQ sort (join1Q-join1F t i) = join1Q-join1F (mapTerm1-mapTermF-joinTermQ sort t) i
    joinTermQ sort (byAxiom axiom f i) = hcomp
      (λ where
         j (i = i0) → join1Q (mapTermF-joinTermQ-∘' f sort (lhs axiom) j)
         j (i = i1) → join1Q (mapTermF-joinTermQ-∘' f sort (rhs axiom) j)
      )
      (byAxiom axiom (λ sort' y → joinTermQ sort' (f sort' y)) i)
    joinTermQ sort (isSetTermQ t1 t2 et et' i j) = isSetTermQ
      (joinTermQ sort t1)
      (joinTermQ sort t2)
      (λ k → joinTermQ sort (et k))
      (λ k → joinTermQ sort (et' k)) i j
    mapTermF-joinTermQ sort (varF t) = varF (joinTermQ sort t)
    mapTermF-joinTermQ sort (join1F t) = join1F (mapTerm1-mapTermF-joinTermQ sort t)
    mapTerm1-mapTermF-joinTermQ sort (term1 o args) = term1 o λ p → mapTermF-joinTermQ (arity o ! p) (args p)
    mapTermF-joinTermQ-∘' f sort (varF y) i = varF (joinTermQ sort (f sort y))
    mapTermF-joinTermQ-∘' f sort (join1F (term1 o args)) i =
      join1F (term1 o λ p → mapTermF-joinTermQ-∘' f (arity o ! p) (args p) i)

    msetTermQ : MSet → MSet
    fst (msetTermQ msetX sortOut) = TermQ (mtyp msetX) sortOut
    snd (msetTermQ msetX sortOut) = isSetTermQ

    mapTermQ : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → TermQ X sort → TermQ Y sort
    -- The following lemmas are needed because we don't use sized types.
    mapTermF-mapTermQ : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → TermF (TermQ X) sort → TermF (TermQ Y) sort
    mapTermF-mapTermQ-∘' : {Z X Y : MType} → (f : ∀ sort → X sort → Y sort) 
      → (g : ∀ sort → Z sort → TermQ X sort)
      → (sort : Sort) → (t : TermF Z sort)
      → mapTermF (λ sort' → mapTermQ f sort' ∘ g sort') sort t ≡ mapTermF-mapTermQ f sort (mapTermF g sort t)

    mapTermQ f sort (varQ x) = varQ (f sort x)
    mapTermQ f sort (join1Q (term1 o args)) = join1Q (term1 o λ p → mapTermQ f (arity o ! p) (args p))
    mapTermQ f sort (join1Q t) = join1Q (mapTermF-mapTermQ f sort t)
    mapTermQ f sort (join1Q-varF t i) = join1Q-varF (mapTermQ f sort t) i
    mapTermQ f sort (join1Q-join1F (term1 o args) i) = join1Q-join1F (term1 o λ p → mapTermF-mapTermQ f (arity o ! p) (args p)) i
    mapTermQ f sort (byAxiom axiom g i) = hcomp
      (λ where
        j (i = i0) → join1Q (mapTermF-mapTermQ-∘' f g sort (lhs axiom) j)
        j (i = i1) → join1Q (mapTermF-mapTermQ-∘' f g sort (rhs axiom) j)
      )
      (byAxiom axiom (λ sort' y → mapTermQ f sort' (g sort' y)) i)
    mapTermQ f sort (isSetTermQ t1 t2 et et' i j) = isSetTermQ
      (mapTermQ f sort t1)
      (mapTermQ f sort t2)
      (λ k → mapTermQ f sort (et k))
      (λ k → mapTermQ f sort (et' k)) i j
    mapTermF-mapTermQ f sort (varF t) = varF (mapTermQ f sort t)
    mapTermF-mapTermQ f sort (join1F (term1 o args)) = join1F (term1 o λ p → mapTermF-mapTermQ f (arity o ! p) (args p))
    mapTermF-mapTermQ-∘' f g sort (varF x) i = varF (mapTermQ f sort (g sort x))
    mapTermF-mapTermQ-∘' f g sort (join1F (term1 o args)) i = join1F (term1 o λ p → mapTermF-mapTermQ-∘' f g (arity o ! p) (args p) i)

    mapTermQ-byAxiom : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort) → ∀ sortOut
      → (axiom : Axiom sortOut) → (g : ∀ sort → mtyp (msetArity axiom) sort → TermQ X sort)
      → PathP
           (λ j → join1Q (mapTermF-mapTermQ-∘' f g sortOut (lhs axiom) j)
                 ≡ join1Q (mapTermF-mapTermQ-∘' f g sortOut (rhs axiom) j)
           )
           (λ i → byAxiom axiom (λ sort y → mapTermQ f sort (g sort y)) i)
           (λ i → mapTermQ f sortOut (byAxiom axiom g i))
    mapTermQ-byAxiom f sortOut axiom g = toPathP (isSetTermQ _ _ _ _)
    
    mapTermQ-id : ∀ {X} → mapTermQ (λ sort → idfun (X sort)) ≡ (λ sort → idfun (TermQ X sort))
    -- The following lemmas are needed because we don't use sized types.
    mapTermF-mapTermQ-id : ∀ {X} → mapTermF-mapTermQ (λ sort → idfun (X sort)) ≡ (λ sort → idfun (TermF (TermQ X) sort))
    mapTermF-mapTermQ-id-∘' : ∀ {Z X : MType}
      → (g : ∀ sort → Z sort → TermQ X sort)
      → (sort : Sort) → (t : TermF Z sort)
      → PathP
           (λ j → {-idfun
                     ( mapTermF (λ sort' x → mapTermQ (λ sort₁ x₁ → x₁) sort' (g sort' x)) sort t
                     ≡ mapTermF-mapTermQ (λ sort₁ x → x) sort (mapTermF g sort t)
                     )-}
                     (mapTermF-mapTermQ-∘' (λ sort₁ x → x) g sort t) j
                 ≡ {-idfun
                     ( mapTermF g sort t
                     ≡ mapTermF g sort t
                     )-}
                     (mapTermF g sort t)
           )
           (λ i → mapTermF (λ sort' → mapTermQ-id i sort' ∘ g sort') sort t)
           λ i → mapTermF-mapTermQ-id i sort (mapTermF g sort t)
    mapTermQ-id i sort (varQ x) = varQ x
    mapTermQ-id i sort (join1Q (term1 o args)) = join1Q (term1 o λ p → mapTermQ-id i (arity o ! p) (args p))
    mapTermQ-id i sort (join1Q t) = join1Q (mapTermF-mapTermQ-id i sort t)
    mapTermQ-id {X = X} i sort (join1Q-varF t j) = join1Q-varF (mapTermQ-id i sort t) j
    mapTermQ-id i sort (join1Q-join1F (term1 o args) j) =
      join1Q-join1F (term1 o λ p → mapTermF-mapTermQ-id i (arity o ! p) (args p)) j
    mapTermQ-id {X = X} k sort (byAxiom axiom f i) = hcomp
      (λ where
        j (i = i0) → join1Q (mapTermF-mapTermQ-id-∘' f sort (lhs axiom) j k)
        j (i = i1) → join1Q (mapTermF-mapTermQ-id-∘' f sort (rhs axiom) j k)
        j (k = i0) → {-idfun
          ( byAxiom axiom (λ sort' y → mapTermQ (λ sort₁ x → x) sort' (f sort' y)) i
          ≡ mapTermQ (λ sort → idfun (X sort)) sort (byAxiom axiom f i)
          )
          (λ j' → mapTermQ-byAxiom {X = X} {Y = X} (λ _ x → x) sort axiom f j' i) j-}
          (mapTermQ-byAxiom {X = X} {Y = X} (λ _ x → x) sort axiom f j i)
        j (k = i1) → {-idfun
          ( byAxiom axiom f i
          ≡ byAxiom axiom f i
          )-}
          byAxiom axiom f i
      )
      (byAxiom axiom (λ sort' y → mapTermQ-id k sort' (f sort' y)) i)
    mapTermQ-id i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
      (mapTermQ-id i sort t1)
      (mapTermQ-id i sort t2)
      (λ k → mapTermQ-id i sort (et k))
      (λ k → mapTermQ-id i sort (et' k)) j k
    mapTermF-mapTermQ-id i sort (varF t) = varF (mapTermQ-id i sort t)
    mapTermF-mapTermQ-id i sort (join1F (term1 o args)) = join1F (term1 o λ p → mapTermF-mapTermQ-id i (arity o ! p) (args p))
    mapTermF-mapTermQ-id-∘' g sort (varF z) j i = varF (mapTermQ-id i sort (g sort z))
    mapTermF-mapTermQ-id-∘' g sort (join1F (term1 o args)) j i =
      join1F (term1 o λ p → mapTermF-mapTermQ-id-∘' g (arity o ! p) (args p) j i)

    --{-# TERMINATING #-}
    mapTermQ-∘ : ∀ {X Y Z : MType}
      → (g : ∀ sort → Y sort → Z sort)
      → (f : ∀ sort → X sort → Y sort)
      → mapTermQ (λ sort → g sort ∘ f sort) ≡ (λ sort → mapTermQ g sort ∘ mapTermQ f sort)
    -- The following lemmas are needed because we don't use sized types.
    mapTermF-mapTermQ-∘ : ∀ {X Y Z : MType}
      → (g : ∀ sort → Y sort → Z sort)
      → (f : ∀ sort → X sort → Y sort)
      → mapTermF-mapTermQ (λ sort → g sort ∘ f sort) ≡ (λ sort → mapTermF-mapTermQ g sort ∘ mapTermF-mapTermQ f sort)
    {-mapTermF-mapTermQ-∘-∘' : ∀ {W X Y Z : MType}
      → (h : ∀ sort → W sort → TermQ X sort)
      → (g : ∀ sort → Y sort → Z sort)
      → (f : ∀ sort → X sort → Y sort)
      → (sort : Sort) → (t : TermF W sort)
      → PathP
           (λ j → {-idfun
                     ( mapTermF (λ sort' x → mapTermQ (λ sort₁ x₁ → x₁) sort' (g sort' x)) sort t
                     ≡ mapTermF-mapTermQ (λ sort₁ x → x) sort (mapTermF g sort t)
                     )-}
                     (mapTermF-mapTermQ-∘' (λ sort' → g sort' ∘ f sort') h sort t) j
                 ≡ {-idfun
                     ( mapTermF g sort t
                     ≡ mapTermF g sort t
                     )-}
                     (mapTermF-mapTermQ-∘' g (λ sort' → {!!}) sort {!!}) j
                     --(mapTermF g sort t)
           )
           (λ i → {!mapTermF (λ sort' → mapTermQ-id i sort' ∘ g sort') sort t!})
           (λ i → {!mapTermF-mapTermQ-id i sort (mapTermF g sort t)!})-}
    mapTermQ-∘ g f i sort (varQ x) = varQ (g sort (f sort x))
    mapTermQ-∘ g f i sort (join1Q (term1 o args)) = join1Q (term1 o λ p → mapTermQ-∘ g f i (arity o ! p) (args p))
    mapTermQ-∘ g f i sort (join1Q t) = join1Q (mapTermF-mapTermQ-∘ g f i sort t)
    mapTermQ-∘ g f i sort (join1Q-varF t j) =
      join1Q-varF (mapTermQ-∘ g f i sort t) j
    mapTermQ-∘ g f i sort (join1Q-join1F (term1 o args) j) =
      join1Q-join1F (term1 o λ p → mapTermF-mapTermQ-∘ g f i (arity o ! p) (args p)) j
    mapTermQ-∘ g f k sort (byAxiom axiom h i) = {!!}
      {-idfun
        (Square
          (λ i → mapTermQ (λ sort₁ → g sort₁ ∘ f sort₁) sort (byAxiom axiom h i))
          (λ i → (mapTermQ g sort ∘ mapTermQ f sort) (byAxiom axiom h i))
          (λ k → join1Q (mapTermF-mapTermQ-∘ g f k sort (mapTermF h sort (lhs axiom))))
          (λ k → join1Q (mapTermF-mapTermQ-∘ g f k sort (mapTermF h sort (rhs axiom))))
        ) (toPathP (isSetTermQ _ _ _ _)) k i-}
    mapTermQ-∘ g f i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
      (mapTermQ-∘ g f i sort t1)
      (mapTermQ-∘ g f i sort t2)
      (λ k → mapTermQ-∘ g f i sort (et k))
      (λ k → mapTermQ-∘ g f i sort (et' k)) j k
    mapTermF-mapTermQ-∘ g f i sort (varF t) = varF (mapTermQ-∘ g f i sort t)
    mapTermF-mapTermQ-∘ g f i sort (join1F (term1 o args)) = join1F (term1 o λ p → mapTermF-mapTermQ-∘ g f i (arity o ! p) (args p))

EqTheory = EqTheory.EqTheory

record Presentation (sign : Signature) : Type where
  constructor presentationQ
  field
    getPresentationF : PresentationF sign
    getEqTheory : EqTheory getPresentationF
