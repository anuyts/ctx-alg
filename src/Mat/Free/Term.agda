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
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.EilenbergMoore

open import Mat.Signature
open import Mat.Free.Presentation

module Mat.Free.Term {sign : Signature} (fmat : PresentationF sign) where

open _≅_
open Category renaming (_∘_ to _⊚_)
open Functor
open Signature sign
open PresentationF fmat
open Algebra renaming (str to algStr)
open AlgebraHom
open IsEMAlgebra

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

ismonadTermF : IsMonad ftrTermF
η ismonadTermF = ηTermF
μ ismonadTermF = μTermF
idl-μ ismonadTermF = makeNatTransPathP (λ i → F-rUnit i) (λ i → ftrTermF) refl
idr-μ ismonadTermF = makeNatTransPathP (λ i → F-lUnit i) (λ i → ftrTermF) lemma
  where lemma : (λ msetX sort t → joinTermF sort (mapTermF (λ sortOut → varF) sort t)) ≡
                (λ msetX sort t → t)
        lemma i msetX sort (varF x) = varF x
        lemma i msetX sort (astF (term1 o args)) = astF (term1 o λ p → lemma i msetX (arity o ! p) (args p))
assoc-μ ismonadTermF = makeNatTransPathP (λ i → F-assoc i) (λ i → ftrTermF) lemma
  where lemma : (λ msetX sort t → joinTermF sort (mapTermF joinTermF sort t)) ≡
                (λ msetX sort t → joinTermF sort (joinTermF sort t))
        lemma i msetX sort (varF ttx) = joinTermF sort ttx
        lemma i msetX sort (astF (term1 o args)) = astF (term1 o λ p → lemma i msetX (arity o ! p) (args p))

monadTermF : Monad catMSet
monadTermF = ftrTermF , ismonadTermF

catModelF : Category ℓ-zero ℓ-zero
catModelF = EMCategory monadTermF

ModelF : Type ℓ-zero
ModelF = ob catModelF

ModelFHom : (mFA mFB : ModelF) → Type ℓ-zero
ModelFHom = Hom[_,_] catModelF

algStrFModel1 : ((algebra msetA α) : Model1) → IsAlgebra ftrTermF msetA
algStrFModel1 (algebra msetA α) sort (varF a) = a
algStrFModel1 (algebra msetA α) sort (astF (term1 o args)) =
  α sort (term1 o λ p → algStrFModel1 (algebra msetA α) (arity o ! p) (args p))

algStrFModel1∘join :
  ((algebra msetA α) : Model1) →
  ∀ sort →
  (tta : TermF (λ sort₁ → TermF (λ sort₂ → fst (msetA sort₂)) sort₁) sort) →
  algStrFModel1 (algebra msetA α) sort (joinTermF sort tta) ≡
  algStrFModel1 (algebra msetA α) sort (mapTermF (algStrFModel1 (algebra msetA α)) sort tta)
algStrFModel1∘join (algebra msetA α) sort (varF ta) = refl
algStrFModel1∘join (algebra msetA α) sort (astF (term1 o args)) =
  cong (α sort) (cong (term1 o) (funExt λ p → algStrFModel1∘join (algebra msetA α) (arity o ! p) (args p)))

model1toF : Model1 → ModelF
carrier (fst (model1toF (algebra msetA α))) = msetA
algStr (fst (model1toF (algebra msetA α))) = algStrFModel1 (algebra msetA α)
str-η (snd (model1toF (algebra msetA α))) = refl
str-μ (snd (model1toF (algebra msetA α))) = funExt λ sort → funExt λ tta → algStrFModel1∘join (algebra msetA α) sort tta

model1toF-ishom : ∀ {(algebra msetA α) (algebra msetB β) : Algebra ftrTerm1} → ((algebraHom f isalgF)
  : Model1Hom (algebra msetA α) (algebra msetB β)) → ∀ sort ta
  → f sort (algStrFModel1 (algebra msetA α) sort ta) ≡ algStrFModel1 (algebra msetB β) sort (mapTermF f sort ta)
model1toF-ishom {algebra msetA α} {algebra msetB β} (algebraHom f commut) sort (varF a) = refl
model1toF-ishom {algebra msetA α} {algebra msetB β} (algebraHom f commut) sort (astF (term1 o args)) =
  f sort (α sort (term1 o (λ p → algStrFModel1 (algebra msetA α) (arity o ! p) (args p))))
    ≡⟨ commut' sort (term1 o λ p → algStrFModel1 (algebra msetA α) (arity o ! p) (args p)) ⟩
  β sort (term1 o (λ p → f (arity o ! p) (algStrFModel1 (algebra msetA α) (arity o ! p) (args p))))
    ≡⟨ cong (β sort) (cong (term1 o) (funExt λ p → model1toF-ishom (algebraHom f commut) (arity o ! p) (args p))) ⟩
  β sort (term1 o (λ p → algStrFModel1 (algebra msetB β) (arity o ! p) (mapTermF f (arity o ! p) (args p)))) ∎
  where commut' : ∀ sort ((term1 o' args') : Term1 (mtyp msetA) sort)
          → f sort (α sort (term1 o' args')) ≡ β sort (term1 o' λ p → f (arity o' ! p) (args' p))
        commut' sort ta i = commut i sort ta

model1toF-hom : ∀ {m1A m1B} → (m1F : Model1Hom m1A m1B) → ModelFHom (model1toF m1A) (model1toF m1B)
carrierHom (model1toF-hom {algebra msetA α} {algebra msetB β} (algebraHom f commut)) = f
strHom (model1toF-hom {algebra msetA α} {algebra msetB β} (algebraHom f commut)) =
  funExt λ sort → funExt λ ta → model1toF-ishom (algebraHom f commut) sort ta

ftrForgetModelF : Functor catModelF catMSet
ftrForgetModelF = ForgetEMAlgebra monadTermF

ftrFreeModelF : Functor catMSet catModelF
ftrFreeModelF = FreeEMAlgebra monadTermF

ftrModel1toF : Functor catModel1 catModelF
F-ob ftrModel1toF = model1toF
F-hom ftrModel1toF = model1toF-hom
F-id ftrModel1toF = AlgebraHom≡ ftrTermF refl
F-seq ftrModel1toF algF algG = AlgebraHom≡ ftrTermF refl

nt1toF : NatTrans ftrTerm1 ftrTermF
N-ob nt1toF msetA sort (term1 o args) = astF (term1 o λ p → varF (args p))
N-hom nt1toF f = refl

ftrModelFto1 : Functor catModelF catModel1
ftrModelFto1 = funcComp {-{D = AlgebrasCategory ftrTermF}{E = catModel1}{C = catModelF}-} (AlgebrasFunctor {F = ftrTerm1} {G = ftrTermF} nt1toF) (ForgetEM monadTermF)
  -- For some reason, this takes forever.
