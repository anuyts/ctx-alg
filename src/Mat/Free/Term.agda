{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.Prod
open import Cubical.Data.W.Indexed
open import Cubical.Data.FinData
open import Cubical.Data.Sum
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to ftrId)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TypeProduct
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation.Base

open import Mat.Signature
open import Mat.Free.Presentation

module Mat.Free.Term {sign : Signature} (fmat : PresentationF sign) where

open _≅_
open Functor
open Signature sign
open PresentationF fmat

data TermF (X : MType) : (sortOut : Sort) → Type
isSetTermF : (msetX : MSet) (sortOut : Sort) → isSet (TermF (mtyp msetX) sortOut)

msetTermF : MSet → MSet
fst (msetTermF msetX sortOut) = TermF (mtyp msetX) sortOut
snd (msetTermF msetX sortOut) = isSetTermF msetX sortOut

data TermF X where
  varF : ∀ {sortOut} → X sortOut → TermF X sortOut
  astF : ∀ {sortOut} → Term1 (TermF X) sortOut → TermF X sortOut

RepTermF : (X : MType) (sortOut : Sort) → Type
RepTermF X sortOut =
  IW (λ sort → X sort ⊎ Operation sort)
    (λ sort → ⊎.elim (λ v → ⊥) λ o → Fin (length (arity o)))
    (λ sort → ⊎.elim (λ v ()) (λ o p → arity o ! p))
    sortOut

toRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut → RepTermF X sortOut
toRepTermF X sortOut (varF v) = node (inl v) (λ ())
toRepTermF X sortOut (astF (term1 o args)) =
  node (inr o) λ p → toRepTermF X (arity o ! p) (args p)

fromRepTermF : (X : MType) (sortOut : Sort) → RepTermF X sortOut → TermF X sortOut
fromRepTermF X sortOut (node (inl v) u) = varF v
fromRepTermF X sortOut (node (inr o) args) = astF (term1 o λ p → fromRepTermF X (arity o ! p) (args p))

fromToRepTermF : (X : MType) (sortOut : Sort) (t : TermF X sortOut)
  → fromRepTermF X sortOut (toRepTermF X sortOut t) ≡ t
fromToRepTermF X sortOut (varF v) = refl
fromToRepTermF X sortOut (astF (term1 o args)) i =
  astF (term1 o λ p → fromToRepTermF X (arity o ! p) (args p) i)

toFromRepTermF : (X : MType) (sortOut : Sort) (rt : RepTermF X sortOut)
  → toRepTermF X sortOut (fromRepTermF X sortOut rt) ≡ rt
toFromRepTermF X sortOut (node (inl v) u) = cong (node (inl v)) (funExt (λ ()))
toFromRepTermF X sortOut (node (inr o) args) i =
  node (inr o) (λ p → toFromRepTermF X (arity o ! p) (args p) i)

isoRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut ≅ RepTermF X sortOut
fun (isoRepTermF X sortOut) = toRepTermF X sortOut
inv (isoRepTermF X sortOut) = fromRepTermF X sortOut
rightInv (isoRepTermF X sortOut) = toFromRepTermF X sortOut
leftInv (isoRepTermF X sortOut) = fromToRepTermF X sortOut

pathRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut ≡ RepTermF X sortOut
pathRepTermF X sortOut = ua (isoToEquiv (isoRepTermF X sortOut))

isSetRepTermF : (msetX : MSet) (sortOut : Sort) → isSet (RepTermF (mtyp msetX) sortOut)
isSetRepTermF msetX sortOut = isOfHLevelSuc-IW 1 (λ sort → isSet⊎ (str (msetX sort)) isSetOperation) sortOut

isSetTermF msetX sortOut = subst⁻ isSet (pathRepTermF (mtyp msetX) sortOut) (isSetRepTermF msetX sortOut)

mapTermF : ∀ {X Y} → (∀ sort → X sort → Y sort) → ∀ sort → TermF X sort → TermF Y sort
mapTermF f sort (varF x) = varF (f sort x)
mapTermF f sort (astF (term1 o args)) = astF (term1 o λ p → mapTermF f (arity o ! p) (args p))

mapTermF-id : ∀ {X} → mapTermF (λ sort → idfun (X sort)) ≡ (λ sort → idfun (TermF X sort))
mapTermF-id i sort (varF x) = varF x
mapTermF-id i sort (astF (term1 o args)) = astF (term1 o (λ p → mapTermF-id i (arity o ! p) (args p)))

mapTermF-∘ : ∀ {X Y Z : MType} → (g : ∀ sort → Y sort → Z sort) → (f : ∀ sort → X sort → Y sort) →
  mapTermF (λ sort → g sort ∘ f sort) ≡ (λ sort → mapTermF g sort ∘ mapTermF f sort)
mapTermF-∘ g f i sort (varF x) = varF (g sort (f sort x))
mapTermF-∘ g f i sort (astF (term1 o args)) = astF (term1 o (λ p → mapTermF-∘ g f i (arity o ! p) (args p)))

ftrTermF : Functor catMSet catMSet
F-ob ftrTermF = msetTermF
F-hom ftrTermF = mapTermF
F-id ftrTermF = mapTermF-id
F-seq ftrTermF f g = mapTermF-∘ g f

-- It's a monad

open NatTrans

ηTermF : NatTrans (ftrId catMSet) ftrTermF
N-ob ηTermF msetX sortOut = varF
N-hom ηTermF {msetX} {msetY} f = refl

joinTermF : ∀ {X} sort → TermF (TermF X) sort → TermF X sort
joinTermF sort (varF t) = t
joinTermF sort (astF (term1 o args)) = astF (term1 o (λ p → joinTermF (arity o ! p) (args p)))

joinTermF-nat : ∀ {X Y : MType} f sort → (t : TermF (TermF X) sort)
  → joinTermF {X = Y} sort (mapTermF (mapTermF f) sort t) ≡ mapTermF f sort (joinTermF sort t)
joinTermF-nat f sort (varF t) = refl
joinTermF-nat f sort (astF (term1 o args)) i = astF (term1 o λ p → joinTermF-nat f (arity o ! p) (args p) i)

μTermF : NatTrans (funcComp ftrTermF ftrTermF) ftrTermF
N-ob μTermF msetX = joinTermF
N-hom μTermF {msetX} {msetY} f = funExt λ sort → funExt λ t → joinTermF-nat f sort t

open IsMonad

monadTermF : IsMonad ftrTermF
η monadTermF = ηTermF
μ monadTermF = μTermF
idl-μ monadTermF = makeNatTransPathP (λ i → F-rUnit i) (λ i → ftrTermF) refl
idr-μ monadTermF = makeNatTransPathP (λ i → F-lUnit i) (λ i → ftrTermF) lemma
  where lemma : (λ msetX sort t → joinTermF sort (mapTermF (λ sortOut → varF) sort t)) ≡
                (λ msetX sort t → t)
        lemma i msetX sort (varF x) = varF x
        lemma i msetX sort (astF (term1 o args)) = astF (term1 o λ p → lemma i msetX (arity o ! p) (args p))
assoc-μ monadTermF = makeNatTransPathP (λ i → F-assoc i) (λ i → ftrTermF) lemma
  where lemma : (λ msetX sort t → joinTermF sort (mapTermF joinTermF sort t)) ≡
                (λ msetX sort t → joinTermF sort (joinTermF sort t))
        lemma i msetX sort (varF ttx) = joinTermF sort ttx
        lemma i msetX sort (astF (term1 o args)) = astF (term1 o λ p → lemma i msetX (arity o ! p) (args p))
