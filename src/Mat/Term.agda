{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure hiding (str)
open import Cubical.Categories.Category
open import Cubical.Categories.Category.Precategory as P
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
open import Mat.Free.Term
open import Mat.Presentation

-- TermQs of the MAT generated by a MAT presentation
module Mat.Term {matsig : MatSignature} (mat : Mat matsig) where

open MatSignature matsig
open Mat
open FreeMat (getFreeMat mat)
open TermF (getFreeMat mat)
open MatEqTheory (getMatEqTheory mat)

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

{- SyntaxQ monad
   -------------
   For the non-equality constructors, `varQ'` and `join1Q'` are all you need.
   However, in `byAxion` we want to easily refer to `joinFQ'` without relying on too much computation (I guess).
   Alternatively, we could suffice with `joinFQ'`, but then we have to state correctness w.r.t. `joinF'` which
   is again a heavy-duty definition.
-}
-- the primes are to signify that the sort is implicit.
data TermQ (X : MType) : MType where
  varQ' : ∀ {sortOut} → X sortOut → TermQ X sortOut
  join1Q' : ∀ {sortOut} → Term1 (TermQ X) sortOut → TermQ X sortOut
  joinFQ' : ∀ {sortOut} → TermF (TermQ X) sortOut → TermQ X sortOut
  joinFQ-varF' : ∀ {sortOut} → (t : TermQ X sortOut) → joinFQ' (varF' t) ≡ t
  joinFQ-join1F' : ∀ {sortOut} → (t : Term1 (TermF (TermQ X)) sortOut)
    → joinFQ' (join1F' t) ≡ join1Q' (mapTerm1 (λ sort → joinFQ') sortOut t)
  byAxiom : ∀ {sortOut : Sort} → (axiom : Axiom sortOut) → (f : ∀ sort → mtyp (msetArity axiom) sort → TermQ X sort)
    → joinFQ' (mapTermF f sortOut (lhs axiom))
    ≡ joinFQ' (mapTermF f sortOut (rhs axiom))
  isSetTermQ : ∀ {sortOut} → isSet (TermQ X sortOut)

varQ : ∀ {X} → (X →M TermQ X)
varQ sort = varQ'

join1Q : ∀ {X} → (Term1 (TermQ X) →M TermQ X)
join1Q sort = join1Q'

joinFQ : ∀ {X} → (TermF (TermQ X) →M TermQ X)
joinFQ sort = joinFQ'

joinFQ-varF : ∀ {X} → joinFQ ∘M varF ≡ idfunM (TermQ X)
joinFQ-varF {X} i sort t = joinFQ-varF' t i

joinFQ-join1F : ∀ {X} → joinFQ {X} ∘M join1F ≡ join1Q ∘M mapTerm1 joinFQ
joinFQ-join1F i sort t = joinFQ-join1F' t i

-- TermQ acting on MSets
msetTermQ : MSet → MSet
fst (msetTermQ msetX sortOut) = TermQ (mtyp msetX) sortOut
snd (msetTermQ msetX sortOut) = isSetTermQ

-- Components of TermQ as a functor
{-# TERMINATING #-}
mapTermQ : ∀ {X Y} → (X →M Y) → (TermQ X →M TermQ Y)
mapTermQ f sort (varQ' x) = varQ' (f sort x)
mapTermQ f sort (join1Q' t) = join1Q' (mapTerm1 (mapTermQ f) sort t)
mapTermQ f sort (joinFQ' t) = joinFQ' (mapTermF (mapTermQ f) sort t)
mapTermQ f sort (joinFQ-varF' t i) = joinFQ-varF' (mapTermQ f sort t) i
mapTermQ f sort (joinFQ-join1F' t i) = ((
    joinFQ ∘M join1F ∘M mapTerm1 (mapTermF (mapTermQ f))
      ≡⟨ cong (_∘M mapTerm1 (mapTermF (mapTermQ f))) joinFQ-join1F ⟩
    join1Q ∘M mapTerm1 joinFQ ∘M mapTerm1 (mapTermF (mapTermQ f))
      ≡⟨ cong (join1Q ∘M_) (sym (mapTerm1-∘ _ _)) ⟩
    join1Q ∘M mapTerm1 (joinFQ ∘M mapTermF (mapTermQ f))
      ≡⟨⟩
    join1Q ∘M mapTerm1 (mapTermQ f ∘M joinFQ)
      ≡⟨ congS (join1Q ∘M_) (mapTerm1-∘ _ _) ⟩
    join1Q ∘M mapTerm1 (mapTermQ f) ∘M mapTerm1 joinFQ ∎
  ) ≡$ sort ≡$S t) i
mapTermQ f sort (byAxiom axiom g i) = hcomp
  (λ where
    j (i = i0) → joinFQ' (mapTermF-∘ (mapTermQ f) g j sort (lhs axiom))
    j (i = i1) → joinFQ' (mapTermF-∘ (mapTermQ f) g j sort (rhs axiom))
  )
  (byAxiom axiom (λ sort' y → mapTermQ f sort' (g sort' y)) i)
mapTermQ f sort (isSetTermQ t1 t2 et et' i j) = isSetTermQ
  (mapTermQ f sort t1)
  (mapTermQ f sort t2)
  (λ k → mapTermQ f sort (et k))
  (λ k → mapTermQ f sort (et' k)) i j

{-# TERMINATING #-}
mapTermQ-id : ∀ {X} → mapTermQ (idfunM X) ≡ idfunM (TermQ X)
mapTermF-mapTermQ-id : ∀ {X} → mapTermF (mapTermQ (idfunM X)) ≡ idfunM (TermF (TermQ X))
mapTerm1-mapTermQ-id : ∀ {X} → mapTerm1 (mapTermQ (idfunM X)) ≡ idfunM (Term1 (TermQ X))
mapTermQ-id i sort (varQ' x) = varQ' x
mapTermQ-id i sort (join1Q' t) = join1Q' (mapTerm1-mapTermQ-id i sort t)
mapTermQ-id i sort (joinFQ' t) = joinFQ' (mapTermF-mapTermQ-id i sort t)
mapTermQ-id {X = X} i sort (joinFQ-varF' t j) = --{!joinFQ-varF' (mapTermQ-id i sort t) j!}
  idfun
    (Square
      (λ j → joinFQ-varF' (mapTermQ (idfunM X) sort t) j)
      (λ j → idfun (TermQ X sort) (joinFQ-varF' t j))
      (λ i → joinFQ' (mapTermF-mapTermQ-id i sort (varF' t)))
      (λ i → mapTermQ-id i sort t)
    ) (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-id i sort (joinFQ-join1F' t j) =
  idfun
    (Square
      (λ j → mapTermQ (λ sort' → idfun _) sort (joinFQ-join1F' t j))
        --(term1 o (λ p → mapTermF (mapTermQ (λ sort₁ x → x)) (arity o ! p) (args p))) j)
      (λ j → joinFQ-join1F' t j)
      (λ i → joinFQ' (mapTermF-mapTermQ-id i sort (join1F' t)))
      (λ i → join1Q' (mapTerm1-mapTermQ-id i sort (mapTerm1 (λ sort₁ → joinFQ') sort t)))
        --(term1 o λ p → joinFQ' (mapTermF-mapTermQ-id i (arity o ! p) (args p)))
    ) (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-id {X = X} k sort (byAxiom axiom f i) =
  idfun
    (Square
      (λ i → mapTermQ (λ _ x → x) sort (byAxiom axiom f i))
      (λ i → byAxiom axiom f i)
      (λ k → joinFQ' (mapTermF-mapTermQ-id k sort (mapTermF f sort (lhs axiom))))
      λ k → joinFQ' (mapTermF-mapTermQ-id k sort (mapTermF f sort (rhs axiom)))
    ) (toPathP (isSetTermQ _ _ _ _)) k i
mapTermQ-id i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (mapTermQ-id i sort t1)
  (mapTermQ-id i sort t2)
  (λ k → mapTermQ-id i sort (et k))
  (λ k → mapTermQ-id i sort (et' k)) j k
mapTermF-mapTermQ-id i = idfun (mapTermF (mapTermQ (λ sort₁ x₁ → x₁)) ≡ (λ _ t → t))
  (cong mapTermF mapTermQ-id ∙ mapTermF-id)
  i
mapTerm1-mapTermQ-id i = idfun (mapTerm1 (mapTermQ (λ sort₁ x₁ → x₁)) ≡ (λ _ t → t))
  (cong mapTerm1 mapTermQ-id ∙ mapTerm1-id)
  i

{-# TERMINATING #-}
mapTermQ-∘ : ∀ {X Y Z : MType} (g : Y →M Z) (f : X →M Y)
  → mapTermQ (g ∘M f) ≡ mapTermQ g ∘M mapTermQ f
mapTermF-mapTermQ-∘ : ∀ {X Y Z : MType} (g : Y →M Z) (f : X →M Y)
  → mapTermF (mapTermQ (g ∘M f)) ≡ mapTermF (mapTermQ g) ∘M mapTermF (mapTermQ f)
mapTerm1-mapTermQ-∘ : ∀ {X Y Z : MType} (g : Y →M Z) (f : X →M Y)
  → mapTerm1 (mapTermQ (g ∘M f)) ≡ mapTerm1 (mapTermQ g) ∘M mapTerm1 (mapTermQ f)
mapTermQ-∘ g f i sort (varQ' x) = varQ' (g sort (f sort x))
mapTermQ-∘ g f i sort (join1Q' t) = join1Q' (mapTerm1-mapTermQ-∘ g f i sort t)
mapTermQ-∘ g f i sort (joinFQ' t) = joinFQ' (mapTermF-mapTermQ-∘ g f i sort t)
mapTermQ-∘ g f i sort (joinFQ-varF' t j) =
  idfun
    (Square
      (λ j → joinFQ-varF' (mapTermQ (λ sort₁ → g sort₁ ∘ f sort₁) sort t) j)
      (λ j → (mapTermQ g sort ∘ mapTermQ f sort) (joinFQ-varF' t j))
      (λ i → joinFQ' (mapTermF-mapTermQ-∘ g f i sort (varF' t)))
      λ i → mapTermQ-∘ g f i sort t
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-∘ g f i sort (joinFQ-join1F' (term1 o args) j) =
  idfun
    (Square
      (λ j → mapTermQ (λ sort' → g sort' ∘ f sort') sort (joinFQ-join1F' (term1 o args) j))
      (λ j → (mapTermQ g sort ∘ mapTermQ f sort) (joinFQ-join1F' (term1 o args) j))
      (λ i → joinFQ' (mapTermF-mapTermQ-∘ g f i sort (join1F' (term1 o args))))
      (λ i → join1Q' (mapTerm1-mapTermQ-∘ g f i sort (mapTerm1 (λ sort₁ → joinFQ') sort (term1 o args))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
mapTermQ-∘ g f k sort (byAxiom axiom h i) =
  idfun
    (Square
      (λ i → mapTermQ (λ sort₁ → g sort₁ ∘ f sort₁) sort (byAxiom axiom h i))
      (λ i → (mapTermQ g sort ∘ mapTermQ f sort) (byAxiom axiom h i))
      (λ k → joinFQ' (mapTermF-mapTermQ-∘ g f k sort (mapTermF h sort (lhs axiom))))
      (λ k → joinFQ' (mapTermF-mapTermQ-∘ g f k sort (mapTermF h sort (rhs axiom))))
    ) (toPathP (isSetTermQ _ _ _ _)) k i
mapTermQ-∘ g f i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (mapTermQ-∘ g f i sort t1)
  (mapTermQ-∘ g f i sort t2)
  (λ k → mapTermQ-∘ g f i sort (et k))
  (λ k → mapTermQ-∘ g f i sort (et' k)) j k
mapTermF-mapTermQ-∘ g f = cong mapTermF (mapTermQ-∘ g f) ∙ mapTermF-∘ (mapTermQ g) (mapTermQ f)
mapTerm1-mapTermQ-∘ g f = cong mapTerm1 (mapTermQ-∘ g f) ∙ mapTerm1-∘ (mapTermQ g) (mapTermQ f)

-- TermQ as a functor on catMSet
ftrTermQ : Functor catMSet catMSet
F-ob ftrTermQ = msetTermQ
F-hom ftrTermQ = mapTermQ
F-id ftrTermQ = mapTermQ-id
F-seq ftrTermQ f g = mapTermQ-∘ g f

-- Components of TermQ as a monad
pureTermQ : {X : MType} → (X →M TermQ X)
pureTermQ = varQ

{-# TERMINATING #-}
joinTermQ : {X : MType} → (TermQ (TermQ X) →M TermQ X)
joinTermQ sort (varQ' t) = t
joinTermQ sort (join1Q' t) = join1Q' (mapTerm1 joinTermQ sort t)
joinTermQ sort (joinFQ' t) = joinFQ' (mapTermF joinTermQ sort t)
joinTermQ sort (joinFQ-varF' t i) = joinFQ-varF' (joinTermQ sort t) i
joinTermQ sort (joinFQ-join1F' t i) = ((
    joinFQ ∘M join1F ∘M mapTerm1 (mapTermF joinTermQ)
      ≡⟨ cong (_∘M mapTerm1 (mapTermF joinTermQ)) joinFQ-join1F ⟩
    join1Q ∘M mapTerm1 joinFQ ∘M mapTerm1 (mapTermF joinTermQ)
      ≡⟨ cong (join1Q ∘M_) (sym (mapTerm1-∘ _ _)) ⟩
    join1Q ∘M mapTerm1 (joinFQ ∘M mapTermF joinTermQ)
      ≡⟨⟩
    join1Q ∘M mapTerm1 (joinTermQ ∘M joinFQ)
      ≡⟨ cong (join1Q ∘M_) (mapTerm1-∘ _ _) ⟩
    join1Q ∘M mapTerm1 joinTermQ ∘M mapTerm1 joinFQ ∎
  ) ≡$ sort ≡$S t) i
joinTermQ sort (byAxiom axiom f i) = hcomp
  (λ where
     j (i = i0) → joinFQ' (mapTermF-∘ joinTermQ f j sort (lhs axiom))
     j (i = i1) → joinFQ' (mapTermF-∘ joinTermQ f j sort (rhs axiom))
  )
  (byAxiom axiom (λ sort' y → joinTermQ sort' (f sort' y)) i)
joinTermQ sort (isSetTermQ t1 t2 et et' i j) = isSetTermQ
  (joinTermQ sort t1)
  (joinTermQ sort t2)
  (λ k → joinTermQ sort (et k))
  (λ k → joinTermQ sort (et' k)) i j

{-# TERMINATING #-}
joinTermQ-nat : ∀ {X Y : MType} → (f : X →M Y) →
  joinTermQ ∘M mapTermQ (mapTermQ f) ≡ mapTermQ f ∘M joinTermQ
mapTermF-joinTermQ-nat : ∀ {X Y : MType} → (f : X →M Y) →
  mapTermF joinTermQ ∘M mapTermF (mapTermQ (mapTermQ f)) ≡ mapTermF (mapTermQ f) ∘M mapTermF joinTermQ
mapTerm1-joinTermQ-nat : ∀ {X Y : MType} → (f : X →M Y) →
  mapTerm1 joinTermQ ∘M mapTerm1 (mapTermQ (mapTermQ f)) ≡ mapTerm1 (mapTermQ f) ∘M mapTerm1 joinTermQ
joinTermQ-nat f i sort (varQ' t) = mapTermQ f sort t
joinTermQ-nat f i sort (join1Q' t) = join1Q' (mapTerm1-joinTermQ-nat f i sort t)
joinTermQ-nat f i sort (joinFQ' t) = joinFQ' (mapTermF-joinTermQ-nat f i sort t)
joinTermQ-nat f i sort (joinFQ-varF' t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ (mapTermQ f) sort) (joinFQ-varF' t j))
      (λ j → (mapTermQ f sort ∘ joinTermQ sort) (joinFQ-varF' t j))
      (λ i → joinFQ' (mapTermF-joinTermQ-nat f i sort (varF' t)))
      (λ i → joinTermQ-nat f i sort t)
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-nat f i sort (joinFQ-join1F' t@(term1 o args) j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ (mapTermQ f) sort) (joinFQ-join1F' (term1 o args) j))
      (λ j → (mapTermQ f sort ∘ joinTermQ sort) (joinFQ-join1F' (term1 o args) j))
      (λ i → joinFQ' (mapTermF-joinTermQ-nat f i sort (join1F' (term1 o args))))
      (λ i → join1Q' (mapTerm1-joinTermQ-nat f i sort (mapTerm1 (λ sort₁ → joinFQ') sort (term1 o args))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-nat f i sort (byAxiom axiom g j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ (mapTermQ f) sort) (byAxiom axiom g j))
      (λ j → (mapTermQ f sort ∘ joinTermQ sort) (byAxiom axiom g j))
      (λ i → joinFQ' (mapTermF-joinTermQ-nat f i sort (mapTermF g sort (lhs axiom))))
      (λ i → joinFQ' (mapTermF-joinTermQ-nat f i sort (mapTermF g sort (rhs axiom))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-nat f i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (joinTermQ-nat f i sort t1)
  (joinTermQ-nat f i sort t2)
  (λ k → joinTermQ-nat f i sort (et k))
  (λ k → joinTermQ-nat f i sort (et' k)) j k
mapTermF-joinTermQ-nat {X} {Y} f =
  mapTermF joinTermQ ∘M mapTermF (mapTermQ (mapTermQ f))
    ≡⟨ sym (mapTermF-∘ _ _) ⟩
  mapTermF (joinTermQ ∘M mapTermQ (mapTermQ f))
    ≡⟨ congS mapTermF (joinTermQ-nat λ sort (x : X sort) → idfun (Y sort) (f sort x)) ⟩
  mapTermF (mapTermQ f ∘M joinTermQ)
    ≡⟨ mapTermF-∘ _ _ ⟩
  mapTermF (mapTermQ f) ∘M mapTermF joinTermQ ∎
mapTerm1-joinTermQ-nat {X} {Y} f =
  mapTerm1 joinTermQ ∘M mapTerm1 (mapTermQ (mapTermQ f))
    ≡⟨ sym (mapTerm1-∘ _ _) ⟩
  mapTerm1 (joinTermQ ∘M mapTermQ (mapTermQ f))
    ≡⟨ congS mapTerm1 (joinTermQ-nat λ sort (x : X sort) → idfun (Y sort) (f sort x)) ⟩
  mapTerm1 (mapTermQ f ∘M joinTermQ)
    ≡⟨ mapTerm1-∘ _ _ ⟩
  mapTerm1 (mapTermQ f) ∘M mapTerm1 joinTermQ ∎

{-# TERMINATING #-}
joinTermQ-lUnit : ∀ {X : MType} →
  joinTermQ ∘M mapTermQ pureTermQ ≡ idfunM (TermQ X)
mapTermF-joinTermQ-lUnit : ∀ {X : MType} →
  mapTermF joinTermQ ∘M mapTermF (mapTermQ pureTermQ) ≡ idfunM (TermF (TermQ X))
mapTerm1-joinTermQ-lUnit : ∀ {X : MType} →
  mapTerm1 joinTermQ ∘M mapTerm1 (mapTermQ pureTermQ) ≡ idfunM (Term1 (TermQ X))
joinTermQ-lUnit i sort (varQ' x) = varQ' x
joinTermQ-lUnit i sort (join1Q' t) = join1Q' (mapTerm1-joinTermQ-lUnit i sort t)
joinTermQ-lUnit i sort (joinFQ' t) = joinFQ' (mapTermF-joinTermQ-lUnit i sort t)
joinTermQ-lUnit i sort (joinFQ-varF' t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ pureTermQ sort) (joinFQ-varF' t j))
      (λ j → joinFQ-varF' t j)
      (λ i → joinFQ' (mapTermF-joinTermQ-lUnit i sort (varF' t)))
      (λ i → joinTermQ-lUnit i sort t)
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-lUnit i sort (joinFQ-join1F' t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ pureTermQ sort) (joinFQ-join1F' t j))
      (λ j → joinFQ-join1F' t j)
      (λ i → joinFQ' (mapTermF-joinTermQ-lUnit i sort (join1F' t)))
      (λ i → join1Q' (mapTerm1-joinTermQ-lUnit i sort (mapTerm1 (λ sort₁ → joinFQ') sort t)))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-lUnit i sort (byAxiom axiom f j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ pureTermQ sort) (byAxiom axiom f j))
      (λ j → byAxiom axiom f j)
      (λ i → joinFQ' (mapTermF-joinTermQ-lUnit i sort (mapTermF f sort (lhs axiom))))
      (λ i → joinFQ' (mapTermF-joinTermQ-lUnit i sort (mapTermF f sort (rhs axiom))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-lUnit i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (joinTermQ-lUnit i sort t1)
  (joinTermQ-lUnit i sort t2)
  (λ j → joinTermQ-lUnit i sort (et j))
  (λ j → joinTermQ-lUnit i sort (et' j)) j k
mapTermF-joinTermQ-lUnit {X} =
  mapTermF joinTermQ ∘M mapTermF (mapTermQ pureTermQ)
    ≡⟨ sym (mapTermF-∘ _ _) ⟩
  mapTermF (joinTermQ ∘M mapTermQ pureTermQ)
    ≡⟨ cong mapTermF joinTermQ-lUnit ⟩
  mapTermF (idfunM (TermQ X))
    ≡⟨ mapTermF-id ⟩
  idfunM (TermF (TermQ X)) ∎
mapTerm1-joinTermQ-lUnit {X} =
  mapTerm1 joinTermQ ∘M mapTerm1 (mapTermQ pureTermQ)
    ≡⟨ sym (mapTerm1-∘ _ _) ⟩
  mapTerm1 (joinTermQ ∘M mapTermQ pureTermQ)
    ≡⟨ cong mapTerm1 joinTermQ-lUnit ⟩
  mapTerm1 (idfunM (TermQ X))
    ≡⟨ mapTerm1-id ⟩
  idfunM (Term1 (TermQ X)) ∎

{-# TERMINATING #-}
joinTermQ-assoc : ∀ {X : MType} →
  joinTermQ {X = X} ∘M mapTermQ joinTermQ ≡ joinTermQ ∘M joinTermQ
mapTermF-joinTermQ-assoc : ∀ {X : MType} →
  mapTermF (joinTermQ {X = X}) ∘M mapTermF (mapTermQ joinTermQ) ≡ mapTermF joinTermQ ∘M mapTermF joinTermQ
mapTerm1-joinTermQ-assoc : ∀ {X : MType} →
  mapTerm1 (joinTermQ {X = X}) ∘M mapTerm1 (mapTermQ joinTermQ) ≡ mapTerm1 joinTermQ ∘M mapTerm1 joinTermQ
joinTermQ-assoc i sort (varQ' t) = joinTermQ sort t
joinTermQ-assoc i sort (join1Q' t) = join1Q' (mapTerm1-joinTermQ-assoc i sort t)
joinTermQ-assoc i sort (joinFQ' t) = joinFQ' (mapTermF-joinTermQ-assoc i sort t)
joinTermQ-assoc i sort (joinFQ-varF' t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ joinTermQ sort) (joinFQ-varF' t j))
      (λ j → (joinTermQ sort ∘ joinTermQ sort) (joinFQ-varF' t j))
      (λ i → joinFQ' (mapTermF-joinTermQ-assoc i sort (varF' t)))
      (λ i → joinTermQ-assoc i sort t)
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-assoc i sort (joinFQ-join1F' t j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ joinTermQ sort) (joinFQ-join1F' t j))
      (λ j → (joinTermQ sort ∘ joinTermQ sort) (joinFQ-join1F' t j))
      (λ i → joinFQ' (mapTermF-joinTermQ-assoc i sort (join1F' t)))
      (λ i → join1Q' (mapTerm1-joinTermQ-assoc i sort (mapTerm1 (λ sort₁ → joinFQ') sort t)))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-assoc i sort (byAxiom axiom f j) =
  idfun
    (Square
      (λ j → (joinTermQ sort ∘ mapTermQ joinTermQ sort) (byAxiom axiom f j))
      (λ j → (joinTermQ sort ∘ joinTermQ sort) (byAxiom axiom f j))
      (λ i → joinFQ' (mapTermF-joinTermQ-assoc i sort (mapTermF f sort (lhs axiom))))
      (λ i → joinFQ' (mapTermF-joinTermQ-assoc i sort (mapTermF f sort (rhs axiom))))
    )
    (toPathP (isSetTermQ _ _ _ _)) i j
joinTermQ-assoc i sort (isSetTermQ t1 t2 et et' j k) = isSetTermQ
  (joinTermQ-assoc i sort t1)
  (joinTermQ-assoc i sort t2)
  (λ j → joinTermQ-assoc i sort (et j))
  (λ j → joinTermQ-assoc i sort (et' j)) j k
mapTermF-joinTermQ-assoc =
  mapTermF joinTermQ ∘M mapTermF (mapTermQ joinTermQ)
    ≡⟨ sym (mapTermF-∘ _ _) ⟩
  mapTermF (joinTermQ ∘M mapTermQ joinTermQ)
    ≡⟨ cong mapTermF joinTermQ-assoc ⟩
  mapTermF (joinTermQ ∘M joinTermQ)
    ≡⟨ mapTermF-∘ _ _ ⟩
  mapTermF joinTermQ ∘M mapTermF joinTermQ ∎
mapTerm1-joinTermQ-assoc =
  mapTerm1 joinTermQ ∘M mapTerm1 (mapTermQ joinTermQ)
    ≡⟨ sym (mapTerm1-∘ _ _) ⟩
  mapTerm1 (joinTermQ ∘M mapTermQ joinTermQ)
    ≡⟨ cong mapTerm1 joinTermQ-assoc ⟩
  mapTerm1 (joinTermQ ∘M joinTermQ)
    ≡⟨ mapTerm1-∘ _ _ ⟩
  mapTerm1 joinTermQ ∘M mapTerm1 joinTermQ ∎

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
termF→Q : ∀ {X : MType} → (TermF X →M TermQ X)
termF→Q sort (varF' x) = varQ' x
termF→Q sort (join1F' t) = join1Q' (mapTerm1 termF→Q sort t)

{-# TERMINATING #-}
termF→Q-nat : ∀ {X Y : MType} → (f : X →M Y) → termF→Q ∘M mapTermF f ≡ mapTermQ f ∘M termF→Q
termF→Q-nat f i sort (varF' x) = varQ' (f sort x)
termF→Q-nat f i sort (join1F' t) = (congS (join1Q ∘M_) (
  mapTerm1 termF→Q ∘M mapTerm1 (mapTermF f)
    ≡⟨ (sym (mapTerm1-∘ _ _)) ⟩
  mapTerm1 (termF→Q ∘M mapTermF f)
    ≡⟨ (cong mapTerm1 (termF→Q-nat f)) ⟩
  mapTerm1 (mapTermQ f ∘M termF→Q)
    ≡⟨ mapTerm1-∘ _ _ ⟩
  mapTerm1 (mapTermQ f) ∘M mapTerm1 termF→Q ∎
  ) ≡$ sort ≡$ t) i

{-# TERMINATING #-}
termF→Q-joinTermF : ∀ {X : MType} → termF→Q {X} ∘M joinTermF ≡ joinTermQ ∘M termF→Q ∘M mapTermF termF→Q
termF→Q-joinTermF i sort (varF' t) = termF→Q sort t
termF→Q-joinTermF i sort (join1F' t) = (congS (join1Q ∘M_) (
  mapTerm1 termF→Q ∘M mapTerm1 joinTermF
    ≡⟨ sym (mapTerm1-∘ _ _) ⟩
  mapTerm1 (termF→Q ∘M joinTermF)
    ≡⟨ congS mapTerm1 termF→Q-joinTermF ⟩
  mapTerm1 (joinTermQ ∘M termF→Q ∘M mapTermF termF→Q)
    ≡⟨ mapTerm1-∘ joinTermQ (termF→Q ∘M mapTermF termF→Q) ⟩
  mapTerm1 joinTermQ ∘M mapTerm1 (termF→Q ∘M mapTermF termF→Q)
    ≡⟨ congS (mapTerm1 joinTermQ ∘M_) (mapTerm1-∘ _ _) ⟩
  mapTerm1 joinTermQ ∘M mapTerm1 termF→Q ∘M mapTerm1 (mapTermF termF→Q) ∎
  ) ≡$ sort ≡$ t) i

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
joinFQ-mapTermF-pureTermQ : ∀ {X : MType} → joinFQ {X} ∘M mapTermF pureTermQ ≡ termF→Q
joinFQ-mapTermF-pureTermQ i sort (varF' x) = joinFQ-varF' (varQ' x) i
joinFQ-mapTermF-pureTermQ i sort (join1F' t) = ((
    joinFQ ∘M join1F ∘M mapTerm1 (mapTermF pureTermQ)
      ≡⟨ congS (_∘M mapTerm1 (mapTermF pureTermQ)) joinFQ-join1F ⟩
    join1Q ∘M mapTerm1 (joinFQ) ∘M mapTerm1 (mapTermF pureTermQ)
      ≡⟨ congS (join1Q ∘M_) (sym (mapTerm1-∘ _ _)) ⟩
    join1Q ∘M mapTerm1 (joinFQ ∘M mapTermF pureTermQ)
      ≡⟨ congS (join1Q ∘M_) (cong mapTerm1 joinFQ-mapTermF-pureTermQ) ⟩
    join1Q ∘M mapTerm1 termF→Q ∎
  ) ≡$ sort ≡$ t) i

-- SyntaxQ object

SyntaxQ : MType
SyntaxQ = TermQ (mtyp msetEmpty)

msetSyntaxQ : MSet
msetSyntaxQ = msetTermQ msetEmpty

syntaxF→Q : ∀ sort → SyntaxF sort → SyntaxQ sort
syntaxF→Q sort = termF→Q sort
