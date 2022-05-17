{-# OPTIONS --cubical --type-in-type #-}
--{-# OPTIONS --cubical --type-in-type --experimental-lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure hiding (str)
open import Cubical.Categories.Category
import Cubical.Categories.Category.Precategory as P
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Instances.Categories
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Constructions.FullSubcategory

open import Mat.Signature
open import Mat.Free.Presentation
import Mat.Free.Term
open import Mat.Presentation

-- TermQs of the MAT generated by a MAT presentation
module Mat.Term {sign : Signature} (mat : Mat sign) where

open Signature sign
open Mat
open FreeMat (getFreeMat mat)
open Mat.Free.Term (getFreeMat mat)
open EqTheory (getEqTheory mat)

open Category hiding (_∘_)
open Functor
open Algebra
open IsMonad
open NatTrans
open IsMonadHom
open IsEMAlgebra
open NaturalBijection
open _⊣_
open AlgebraHom
open _≅_
private
  module P≅ = P.PrecatIso

-- SyntaxQ monad
data TermQ (X : MType) : (sort : Sort) → Type where
  var : ∀ {sortOut} → X sortOut → TermQ X sortOut
  ast : ∀ {sortOut} → Term1 (TermQ X) sortOut → TermQ X sortOut
  joinFQ : ∀ {sortOut} → TermF (TermQ X) sortOut → TermQ X sortOut
  joinFQ-varF : ∀ {sortOut} → (t : TermQ X sortOut) → joinFQ (varF t) ≡ t
  joinFQ-astF : ∀ {sortOut} → (t : Term1 (TermF (TermQ X)) sortOut)
    → joinFQ (astF t) ≡ ast (mapTerm1 (λ sort → joinFQ) sortOut t)
  byAxiom : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → TermQ X sort)
    → joinFQ (mapTermF f sortOut (lhs axiom))
    ≡ joinFQ (mapTermF f sortOut (rhs axiom))
  isSetTermQ : ∀ {sortOut} → isSet (TermQ X sortOut)

-- TermQ acting on MSets
msetTermQ : MSet → MSet
fst (msetTermQ msetX sortOut) = TermQ (mtyp msetX) sortOut
snd (msetTermQ msetX sortOut) = isSetTermQ

-- Components of TermQ as a functor
{-# TERMINATING #-}
mapTermQ : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → TermQ X sort → TermQ Y sort
mapTermQ f sort (var x) = var (f sort x)
mapTermQ f sort (ast t) = ast (mapTerm1 (mapTermQ f) sort t)
mapTermQ f sort (joinFQ t) = joinFQ (mapTermF (mapTermQ f) sort t)
mapTermQ f sort (joinFQ-varF t i) = joinFQ-varF (mapTermQ f sort t) i
mapTermQ f sort (joinFQ-astF t i) = joinFQ-astF (mapTerm1 (mapTermF (mapTermQ f)) sort t) i
mapTermQ f sort (byAxiom axiom g i) = hcomp
  (λ where
    j (i = i0) → joinFQ (mapTermF-∘ (mapTermQ f) g j sort (lhs axiom))
    j (i = i1) → joinFQ (mapTermF-∘ (mapTermQ f) g j sort (rhs axiom))
  )
  (byAxiom axiom (λ sort' y → mapTermQ f sort' (g sort' y)) i)
mapTermQ f sort (isSetTermQ t1 t2 et et' i j) = isSetTermQ
  (mapTermQ f sort t1)
  (mapTermQ f sort t2)
  (λ k → mapTermQ f sort (et k))
  (λ k → mapTermQ f sort (et' k)) i j

{-# TERMINATING #-}
mapTermQ-id : ∀ {X} → mapTermQ (λ sort → idfun (X sort)) ≡ (λ sort → idfun (TermQ X sort))
mapTermF-mapTermQ-id : ∀ {X} → mapTermF (mapTermQ (λ sort → idfun (X sort))) ≡ (λ sort → idfun (TermF (TermQ X) sort))
mapTermQ-id i sort (var x) = var x
{-
mapTermQ-id i sort (ast t) = ast (mapTerm1 (mapTermQ-id i) sort t)
mapTermQ-id i sort (joinFQ t) = joinFQ (mapTermF-mapTermQ-id i sort t)
mapTermQ-id {X = X} i sort (joinFQ-varF t j) = --{!joinFQ-varF (mapTermQ-id i sort t) j!}
  idfun
    (Square
      (λ j → joinFQ-varF (mapTermQ (λ sort₁ → idfun (X sort₁)) sort t) j)
      (λ j → idfun (TermQ X sort) (joinFQ-varF t j))
      (λ i → joinFQ (mapTermF-mapTermQ-id i sort (varF t)))
      (λ i → mapTermQ-id i sort t)
    ) (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-id i sort (joinFQ-astF (term1 o args) j) =
  idfun
    (Square
      (λ j → joinFQ-astF (term1 o (λ p → mapTermF (mapTermQ (λ sort₁ x → x)) (arity o ! p) (args p))) j)
      (λ j → joinFQ-astF (term1 o args) j)
      (λ i →  joinFQ (mapTermF-mapTermQ-id i sort (astF (term1 o args)))
      )
      (λ i →  ast (term1 o λ p → joinFQ (mapTermF-mapTermQ-id i (arity o ! p) (args p)))
      )
    ) (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-id {X = X} k sort (byAxiom axiom f i) =
  idfun
    (Square
      (λ i → mapTermQ (λ _ x → x) sort (byAxiom axiom f i))
      (λ i → byAxiom axiom f i)
      (λ k → joinFQ (mapTermF-mapTermQ-id k sort (mapTermF f sort (lhs axiom))))
      λ k → joinFQ (mapTermF-mapTermQ-id k sort (mapTermF f sort (rhs axiom)))
    ) (toPathP (isSetTermQ _ _ _ _)) k i
mapTermQ-id i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (mapTermQ-id i sort t1)
  (mapTermQ-id i sort t2)
  (λ k → mapTermQ-id i sort (et k))
  (λ k → mapTermQ-id i sort (et' k)) j k
mapTermF-mapTermQ-id i = idfun (mapTermF (mapTermQ (λ sort₁ x₁ → x₁)) ≡ (λ _ t → t))
  (cong mapTermF mapTermQ-id ∙ mapTermF-id)
  i

{-# TERMINATING #-}
mapTermQ-∘ : ∀ {X Y Z : MType}
  → (g : ∀ sort → Y sort → Z sort)
  → (f : ∀ sort → X sort → Y sort)
  → mapTermQ (λ sort → g sort ∘ f sort) ≡ (λ sort → mapTermQ g sort ∘ mapTermQ f sort)
mapTermF-mapTermQ-∘ : ∀ {X Y Z : MType}
  → (g : ∀ sort → Y sort → Z sort)
  → (f : ∀ sort → X sort → Y sort)
  → mapTermF (mapTermQ (λ sort → g sort ∘ f sort)) ≡ (λ sort → mapTermF (mapTermQ g) sort ∘ mapTermF (mapTermQ f) sort)
mapTermQ-∘ g f i sort (var x) = var (g sort (f sort x))
mapTermQ-∘ g f i sort (ast t) = ast (mapTerm1 (mapTermQ-∘ g f i) sort t)
mapTermQ-∘ g f i sort (joinFQ t) = joinFQ (mapTermF-mapTermQ-∘ g f i sort t)
mapTermQ-∘ g f i sort (joinFQ-varF t j) =
  idfun
    (Square
      (λ j → joinFQ-varF (mapTermQ (λ sort₁ → g sort₁ ∘ f sort₁) sort t) j)
      (λ j → (mapTermQ g sort ∘ mapTermQ f sort) (joinFQ-varF t j))
      (λ i → joinFQ (mapTermF-mapTermQ-∘ g f i sort (varF t)))
      λ i → mapTermQ-∘ g f i sort t
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-∘ g f i sort (joinFQ-astF (term1 o args) j) =
  idfun
    (Square
      (λ j → joinFQ-astF (term1 o (λ p →
        mapTermF (mapTermQ (λ sort₁ x → g sort₁ (f sort₁ x))) (arity o ! p) (args p))) j)
      (λ j → joinFQ-astF (term1 o (λ p →
        mapTermF (mapTermQ g) (arity o ! p) (mapTermF (mapTermQ f) (arity o ! p) (args p)))) j)
      (λ i → joinFQ (mapTermF-mapTermQ-∘ g f i sort (astF (term1 o args))))
      (λ i → ast (term1 o λ p → joinFQ (mapTermF-mapTermQ-∘ g f i (arity o ! p) (args p))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-∘ g f k sort (byAxiom axiom h i) =
  idfun
    (Square
      (λ i → mapTermQ (λ sort₁ → g sort₁ ∘ f sort₁) sort (byAxiom axiom h i))
      (λ i → (mapTermQ g sort ∘ mapTermQ f sort) (byAxiom axiom h i))
      (λ k → joinFQ (mapTermF-mapTermQ-∘ g f k sort (mapTermF h sort (lhs axiom))))
      (λ k → joinFQ (mapTermF-mapTermQ-∘ g f k sort (mapTermF h sort (rhs axiom))))
    ) (toPathP (isSetTermQ _ _ _ _)) k i
mapTermQ-∘ g f i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (mapTermQ-∘ g f i sort t1)
  (mapTermQ-∘ g f i sort t2)
  (λ k → mapTermQ-∘ g f i sort (et k))
  (λ k → mapTermQ-∘ g f i sort (et' k)) j k
mapTermF-mapTermQ-∘ g f = cong mapTermF (mapTermQ-∘ g f) ∙ mapTermF-∘ (mapTermQ g) (mapTermQ f)

-- TermQ as a functor on catMSet
ftrTermQ : Functor catMSet catMSet
F-ob ftrTermQ = msetTermQ
F-hom ftrTermQ = mapTermQ
F-id ftrTermQ = mapTermQ-id
F-seq ftrTermQ f g = mapTermQ-∘ g f

-- Components of TermQ as a monad
pureTermQ : {X : MType} → (sort : Sort) → X sort → TermQ X sort
pureTermQ sort x = var x

{-# TERMINATING #-}
joinTermQ : {X : MType} → (sort : Sort) → TermQ (TermQ X) sort → TermQ X sort
joinTermQ sort (var t) = t
joinTermQ sort (ast t) = ast (mapTerm1 joinTermQ sort t)
joinTermQ sort (joinFQ t) = joinFQ (mapTermF joinTermQ sort t)
joinTermQ sort (joinFQ-varF t i) = joinFQ-varF (joinTermQ sort t) i
joinTermQ sort (joinFQ-astF t i) = joinFQ-astF (mapTerm1 (mapTermF joinTermQ) sort t) i
joinTermQ sort (byAxiom axiom f i) = hcomp
  (λ where
     j (i = i0) → joinFQ (mapTermF-∘ joinTermQ f j sort (lhs axiom))
     j (i = i1) → joinFQ (mapTermF-∘ joinTermQ f j sort (rhs axiom))
  )
  (byAxiom axiom (λ sort' y → joinTermQ sort' (f sort' y)) i)
joinTermQ sort (isSetTermQ t1 t2 et et' i j) = isSetTermQ
  (joinTermQ sort t1)
  (joinTermQ sort t2)
  (λ k → joinTermQ sort (et k))
  (λ k → joinTermQ sort (et' k)) i j

{-# TERMINATING #-}
joinTermQ-nat : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort) →
  (λ sort → joinTermQ sort ∘ mapTermQ (mapTermQ f) sort)
  ≡ (λ sort → mapTermQ f sort ∘ joinTermQ sort)
mapTermF-joinTermQ-nat : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort) →
  (λ sort → mapTermF joinTermQ sort ∘ mapTermF (mapTermQ (mapTermQ f)) sort)
  ≡ (λ sort → mapTermF (mapTermQ f) sort ∘ mapTermF joinTermQ sort)
joinTermQ-nat f i sort (var t) = mapTermQ f sort t
joinTermQ-nat f i sort (ast t) = ast (mapTerm1 (joinTermQ-nat f i) sort t)
joinTermQ-nat f i sort (joinFQ t) = joinFQ (mapTermF-joinTermQ-nat f i sort t)
joinTermQ-nat f i sort (joinFQ-varF t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ (mapTermQ f) sort) (joinFQ-varF t j))
      (λ j → (mapTermQ f sort ∘ joinTermQ sort) (joinFQ-varF t j))
      (λ i → joinFQ (mapTermF-joinTermQ-nat f i sort (varF t)))
      (λ i → joinTermQ-nat f i sort t)
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-nat f i sort (joinFQ-astF t@(term1 o args) j) =
  idfun
    (Square
      (λ j → joinFQ-astF (mapTerm1 (mapTermF joinTermQ) sort
        (mapTerm1 (mapTermF (mapTermQ (mapTermQ f))) sort (term1 o args))) j)
      (λ j → joinFQ-astF (mapTerm1 (mapTermF (mapTermQ f)) sort
        (mapTerm1 (mapTermF joinTermQ) sort (term1 o args))) j)
      (λ i → joinFQ (mapTermF-joinTermQ-nat f i sort (astF t)))
      (λ i → ast (mapTerm1 (joinTermQ-nat f i) sort (mapTerm1 (λ sort₁ → joinFQ) sort t)))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-nat f i sort (byAxiom axiom g j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ (mapTermQ f) sort) (byAxiom axiom g j))
      (λ j → (mapTermQ f sort ∘ joinTermQ sort) (byAxiom axiom g j))
      (λ i → joinFQ (mapTermF-joinTermQ-nat f i sort (mapTermF g sort (lhs axiom))))
      (λ i → joinFQ (mapTermF-joinTermQ-nat f i sort (mapTermF g sort (rhs axiom))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-nat f i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (joinTermQ-nat f i sort t1)
  (joinTermQ-nat f i sort t2)
  (λ k → joinTermQ-nat f i sort (et k))
  (λ k → joinTermQ-nat f i sort (et' k)) j k
mapTermF-joinTermQ-nat f =
  (λ sort → mapTermF joinTermQ sort ∘ mapTermF (mapTermQ (mapTermQ f)) sort)
    ≡⟨ sym (mapTermF-∘ joinTermQ (mapTermQ (mapTermQ f))) ⟩
  mapTermF (λ sort → joinTermQ sort ∘ mapTermQ (mapTermQ f) sort)
    ≡⟨ cong mapTermF (joinTermQ-nat f) ⟩
  mapTermF (λ sort → mapTermQ f sort ∘ joinTermQ sort)
    ≡⟨ mapTermF-∘ (mapTermQ f) joinTermQ ⟩
  (λ sort → mapTermF (mapTermQ f) sort ∘ mapTermF joinTermQ sort) ∎

{-# TERMINATING #-}
joinTermQ-lUnit : ∀ {X : MType} →
  (λ sort → joinTermQ sort ∘ mapTermQ pureTermQ sort) ≡ λ (sort : Sort) → idfun (TermQ X sort)
mapTermF-joinTermQ-lUnit : ∀ {X : MType} →
  (λ sort → mapTermF joinTermQ sort ∘ mapTermF (mapTermQ pureTermQ) sort) ≡ λ (sort : Sort) → idfun (TermF (TermQ X) sort)
joinTermQ-lUnit i sort (var x) = var x
joinTermQ-lUnit i sort (ast t) = ast (mapTerm1 (joinTermQ-lUnit i) sort t)
joinTermQ-lUnit i sort (joinFQ t) = joinFQ (mapTermF-joinTermQ-lUnit i sort t)
joinTermQ-lUnit i sort (joinFQ-varF t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ pureTermQ sort) (joinFQ-varF t j))
      (λ j → joinFQ-varF t j)
      (λ i → joinFQ (varF (joinTermQ-lUnit i sort t)))
      (λ i → joinTermQ-lUnit i sort t)
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-lUnit i sort (joinFQ-astF t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ pureTermQ sort) (joinFQ-astF t j))
      (λ j → joinFQ-astF t j)
      (λ i → joinFQ (astF (mapTerm1 (mapTermF-joinTermQ-lUnit i) sort t)))
      (λ i → ast (mapTerm1 (joinTermQ-lUnit i) sort (mapTerm1 (λ sort₁ → joinFQ) sort t)))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-lUnit i sort (byAxiom axiom f j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ pureTermQ sort) (byAxiom axiom f j))
      (λ j → byAxiom axiom f j)
      (λ i → joinFQ (mapTermF-joinTermQ-lUnit i sort (mapTermF f sort (lhs axiom))))
      (λ i → joinFQ (mapTermF-joinTermQ-lUnit i sort (mapTermF f sort (rhs axiom))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-lUnit i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (joinTermQ-lUnit i sort t1)
  (joinTermQ-lUnit i sort t2)
  (λ j → joinTermQ-lUnit i sort (et j))
  (λ j → joinTermQ-lUnit i sort (et' j)) j k
mapTermF-joinTermQ-lUnit i sort (varF t) = varF (joinTermQ-lUnit i sort t)
mapTermF-joinTermQ-lUnit i sort (astF t) = astF (mapTerm1 (mapTermF-joinTermQ-lUnit i) sort t)

{-# TERMINATING #-}
joinTermQ-assoc : ∀ {X : MType} →
  (λ (sort : Sort) → joinTermQ {X = X} sort ∘ mapTermQ joinTermQ sort) ≡ (λ sort → joinTermQ sort ∘ joinTermQ sort)
mapTermF-joinTermQ-assoc : ∀ {X : MType} →
  (λ (sort : Sort) → mapTermF (joinTermQ {X = X}) sort ∘ mapTermF (mapTermQ joinTermQ) sort)
  ≡ (λ sort → mapTermF joinTermQ sort ∘ mapTermF joinTermQ sort)
joinTermQ-assoc i sort (var t) = joinTermQ sort t
joinTermQ-assoc i sort (ast t) = ast (mapTerm1 (joinTermQ-assoc i) sort t)
joinTermQ-assoc i sort (joinFQ t) = joinFQ (mapTermF-joinTermQ-assoc i sort t)
joinTermQ-assoc i sort (joinFQ-varF t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ joinTermQ sort) (joinFQ-varF t j))
      (λ j → (joinTermQ sort ∘ joinTermQ sort) (joinFQ-varF t j))
      (λ i → joinFQ (varF (joinTermQ-assoc i sort t)))
      (λ i → joinTermQ-assoc i sort t)
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-assoc i sort (joinFQ-astF t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ joinTermQ sort) (joinFQ-astF t j))
      (λ j → (joinTermQ sort ∘ joinTermQ sort) (joinFQ-astF t j))
      (λ i → joinFQ (astF (mapTerm1 (mapTermF-joinTermQ-assoc i) sort t)))
      (λ i → ast (mapTerm1 (joinTermQ-assoc i) sort (mapTerm1 (λ sort₁ → joinFQ) sort t)))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-assoc i sort (byAxiom axiom f j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ joinTermQ sort) (byAxiom axiom f j))
      (λ j → (joinTermQ sort ∘ joinTermQ sort) (byAxiom axiom f j))
      (λ i → joinFQ (mapTermF-joinTermQ-assoc i sort (mapTermF f sort (lhs axiom))))
      (λ i → joinFQ (mapTermF-joinTermQ-assoc i sort (mapTermF f sort (rhs axiom))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-assoc i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (joinTermQ-assoc i sort t1)
  (joinTermQ-assoc i sort t2)
  (λ j → joinTermQ-assoc i sort (et j))
  (λ j → joinTermQ-assoc i sort (et' j)) j k
mapTermF-joinTermQ-assoc i sort (varF t) = varF (joinTermQ-assoc i sort t)
mapTermF-joinTermQ-assoc i sort (astF t) = astF (mapTerm1 (mapTermF-joinTermQ-assoc i) sort t)

-- TermQ as a monad
ismonadTermQ : IsMonad ftrTermQ
N-ob (η ismonadTermQ) msetX = pureTermQ
N-hom (η ismonadTermQ) f = refl
N-ob (μ ismonadTermQ) msetX = joinTermQ
N-hom (μ ismonadTermQ) {msetX}{msetY} f = joinTermQ-nat f
idl-μ ismonadTermQ = makeNatTransPathP F-rUnit (λ i → ftrTermQ) refl
idr-μ ismonadTermQ = makeNatTransPathP F-lUnit (λ i → ftrTermQ) (funExt λ msetX → joinTermQ-lUnit)
assoc-μ ismonadTermQ = makeNatTransPathP F-assoc (λ i → ftrTermQ) (funExt λ msetX → joinTermQ-assoc)

monadTermQ : Monad catMSet
monadTermQ = ftrTermQ , ismonadTermQ

------------

{-# TERMINATING #-}
termF→Q : ∀ {X : MType} sort → TermF X sort → TermQ X sort
termF→Q sort (varF x) = var x
termF→Q sort (astF t) = ast (mapTerm1 termF→Q sort t)

{-# TERMINATING #-}
termF→Q-nat : ∀ {X Y : MType} → (f : ∀ sort → X sort → Y sort)
  → (λ (sort : Sort) → termF→Q sort ∘ mapTermF f sort)
   ≡ (λ (sort : Sort) → mapTermQ f sort ∘ termF→Q sort)
termF→Q-nat f i sort (varF x) = var (f sort x)
termF→Q-nat f i sort (astF t) = ast (mapTerm1 (termF→Q-nat f i) sort t)

{-# TERMINATING #-}
termF→Q-joinTermF : ∀ {X : MType}
 → (λ (sort : Sort) → termF→Q {X} sort ∘ joinTermF sort)
  ≡ (λ (sort : Sort) → joinTermQ sort ∘ termF→Q sort ∘ mapTermF termF→Q sort)
termF→Q-joinTermF i sort (varF t) = termF→Q sort t
termF→Q-joinTermF i sort (astF t) = ast (mapTerm1 (termF→Q-joinTermF i) sort t)

ntTermF→Q : NatTrans ftrTermF ftrTermQ
N-ob ntTermF→Q msetX = termF→Q
N-hom ntTermF→Q {msetX} {msetY} f = termF→Q-nat f

ismonadTermF→Q : IsMonadHom monadTermF monadTermQ ntTermF→Q
N-η ismonadTermF→Q = makeNatTransPath refl
N-μ ismonadTermF→Q = makeNatTransPath (funExt λ msetX → termF→Q-joinTermF)

monadTermF→Q : MonadHom monadTermF monadTermQ
fst monadTermF→Q = ntTermF→Q
snd monadTermF→Q = ismonadTermF→Q

{-# TERMINATING #-}
joinFQ-mapTermF-pureTermQ : ∀ {X : MType} → (λ (sort : Sort) → joinFQ {X} ∘ mapTermF pureTermQ sort) ≡ termF→Q
joinFQ-mapTermF-pureTermQ i sort (varF x) = joinFQ-varF (var x) i
joinFQ-mapTermF-pureTermQ i sort (astF t) = idfun
  ( (joinFQ ∘ mapTermF pureTermQ sort) (astF t)
  ≡ ast (mapTerm1 termF→Q sort t)
  )
  (
    joinFQ (astF (mapTerm1 (mapTermF pureTermQ) sort t))
      ≡⟨ joinFQ-astF (mapTerm1 (mapTermF pureTermQ) sort t) ⟩
    ast (mapTerm1 (λ sort₁ → joinFQ) sort (mapTerm1 (mapTermF pureTermQ) sort t))
      ≡⟨⟩
    ast (mapTerm1 (λ sort' → joinFQ ∘ mapTermF pureTermQ sort') sort t)
      ≡⟨ cong ast (cong (λ f → mapTerm1 f sort t) joinFQ-mapTermF-pureTermQ) ⟩
    ast (mapTerm1 termF→Q sort t) ∎
  )
  i

-- SyntaxQ object

SyntaxQ : MType
SyntaxQ = TermQ (mtyp msetEmpty)

msetSyntaxQ : MSet
msetSyntaxQ = msetTermQ msetEmpty

syntaxF→Q : ∀ sort → SyntaxF sort → SyntaxQ sort
syntaxF→Q sort = termF→Q sort
-}
