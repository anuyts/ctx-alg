{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties
open import Cubical.Data.List.FinData renaming (lookup to _!_)
open import Cubical.Data.List.Dependent renaming (lookupP to _!P_)
open import Cubical.Data.Prod
open import Cubical.Data.W.Indexed
open import Cubical.Data.FinData
open import Cubical.Data.Sum
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Category.Precategory hiding (_[_,_] ; seq')
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to ftrId)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Categories
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Limits.Initial

open import Mat.Signature
open import Mat.Free.Presentation

-- Terms of the free MAT generated by a free MAT presentation
module Mat.Free.Term where

module TermF {matsig : MatSignature} (fmat : FreeMat matsig) where
    open _≅_
    open Category renaming (_∘_ to _⊚_)
    open Functor
    open NatTrans
    open MatSignature matsig
    open FreeMat fmat
    open Algebra renaming (str to algStr)
    open AlgebraHom
    open IsEMAlgebra
    open NaturalBijection
    open _⊣_

    -- Free syntax monad
    data TermF (X : MType) : MType
    isSetTermF : (msetX : MSet) (sortOut : Sort) → isSet (TermF (mtyp msetX) sortOut)

    -- TermF acting on MSets
    msetTermF : MSet → MSet
    fst (msetTermF msetX sortOut) = TermF (mtyp msetX) sortOut
    snd (msetTermF msetX sortOut) = isSetTermF msetX sortOut

    data TermF X where
      -- the primes are to signify that the sort is implicit.
      varF' : ∀ {sortOut} → X sortOut → TermF X sortOut
      join1F' : ∀ {sortOut} → Term1 (TermF X) sortOut → TermF X sortOut

    varF : ∀ {X} → (X →M TermF X)
    varF sort = varF'

    join1F : ∀ {X} → (Term1 (TermF X) →M TermF X)
    join1F sort = join1F'

    arvarF' : ∀ {arity : Arity} → (m : Fin (length arity)) → TermF (mtyp (arity2mset arity)) (arity ! m)
    arvarF' m = varF' (m , refl)
    pattern _$1_ o args = join1F' (term1 o args)
    infixr 4 _$1_

    -- TermF is really an IW type
    module _ where
      RepTermF : (X : MType) → MType
      RepTermF X sortOut =
        IW (λ sort → X sort ⊎ Operation sort)
          (λ sort → ⊎.elim (λ v → ⊥) λ o → Fin (length (arity o)))
          (λ sort → ⊎.elim (λ v ()) (λ o p → arity o ! p))
          sortOut

      {-# TERMINATING #-}
      toRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut → RepTermF X sortOut
      toRepTermF X sortOut (varF' v) = node (inl v) (λ ())
      toRepTermF X sortOut (o $1 args) = node (inr o) λ p → mapOverIdfun (toRepTermF X) (arity o) args !P p

      {-# TERMINATING #-}
      fromRepTermF : (X : MType) (sortOut : Sort) → RepTermF X sortOut → TermF X sortOut
      fromRepTermF X sortOut (node (inl v) u) = varF' v
      fromRepTermF X sortOut (node (inr o) args) =
        o $1 mapOverIdfun (fromRepTermF X) (arity o) (tabulateOverLookup (arity o) args)

      {-# TERMINATING #-}
      fromToRepTermF : (X : MType) (sortOut : Sort) (t : TermF X sortOut)
        → fromRepTermF X sortOut (toRepTermF X sortOut t) ≡ t
      fromToRepTermF X sortOut (varF' v) = refl
      fromToRepTermF X sortOut (join1F' (term1 o args)) =
        cong join1F' (cong (term1 o) (
          mapOverIdfun (fromRepTermF X) (arity o) (tabulateOverLookup (arity o) (_!P_ (mapOverIdfun (toRepTermF X) (arity o) args)))
            ≡⟨ cong (mapOverIdfun _ _) (tabulateOverLookup-lookupP (mapOverIdfun (toRepTermF X) (arity o) args)) ⟩
          mapOverIdfun (fromRepTermF X) (arity o) (mapOverIdfun (toRepTermF X) (arity o) args)
            ≡⟨ sym (mapOverIdfun-∘ (fromRepTermF X) (toRepTermF X) (arity o)) ≡$ args ⟩
          mapOverIdfun (λ a → fromRepTermF X a ∘ toRepTermF X a) (arity o) args
            ≡⟨ (cong mapOverIdfun (funExt λ sort → funExt λ t → fromToRepTermF X sort t) ≡$ arity o) ≡$ args ⟩
          mapOverIdfun (λ x x₁ → x₁) (arity o) args
            ≡⟨ mapOverIdfun-idfun (arity o) ≡$ args ⟩
          args ∎
        ))

    {-# TERMINATING #-} -- this pragma is ignored if I put this definition also in the module :-O
    toFromRepTermF : (X : MType) (sortOut : Sort) (rt : RepTermF X sortOut)
        → toRepTermF X sortOut (fromRepTermF X sortOut rt) ≡ rt
    toFromRepTermF X sortOut (node (inl v) u) = cong (node (inl v)) (funExt (λ ()))
    toFromRepTermF X sortOut (node (inr o) args) = cong {B = λ _ → RepTermF X sortOut} (node (inr o)) (
          _!P_ (mapOverIdfun (toRepTermF X) (arity o) (mapOverIdfun (fromRepTermF X) (arity o) (tabulateOverLookup (arity o) args)))
            ≡⟨ cong _!P_ (sym (mapOverIdfun-∘
                 (toRepTermF X)
                 (fromRepTermF X)
                 (arity o)
                 ≡$ (tabulateOverLookup (arity o) args)
               )) ⟩
          _!P_ (mapOverIdfun (λ sort → toRepTermF X sort ∘ fromRepTermF X sort) (arity o) (tabulateOverLookup (arity o) args))
            ≡⟨ cong _!P_
                 ((cong mapOverIdfun (funExt λ sort → funExt λ t → toFromRepTermF X sort t)
                   ≡$ arity o)
                   ≡$ tabulateOverLookup (arity o) args) ⟩
          _!P_ (mapOverIdfun (λ x x₁ → x₁) (arity o) (tabulateOverLookup (arity o) args))
            ≡⟨ cong (_!P_ {B = RepTermF X}) (mapOverIdfun-idfun (arity o) ≡$ tabulateOverLookup (arity o) args) ⟩
          _!P_ (tabulateOverLookup (arity o) args)
            ≡⟨ lookupP-tabulateOverLookup (RepTermF X) (arity o) args ⟩
          args ∎
        )

    module _ where
      isoRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut ≅ RepTermF X sortOut
      fun (isoRepTermF X sortOut) = toRepTermF X sortOut
      inv (isoRepTermF X sortOut) = fromRepTermF X sortOut
      rightInv (isoRepTermF X sortOut) = toFromRepTermF X sortOut
      leftInv (isoRepTermF X sortOut) = fromToRepTermF X sortOut

      --pathRepTermF : (X : MType) (sortOut : Sort) → TermF X sortOut ≡ RepTermF X sortOut
      --pathRepTermF X sortOut = ua (isoToEquiv (isoRepTermF X sortOut))

      isSetRepTermF : (msetX : MSet) (sortOut : Sort) → isSet (RepTermF (mtyp msetX) sortOut)
      isSetRepTermF msetX sortOut = isOfHLevelSuc-IW 1 (λ sort → isSet⊎ (str (msetX sort)) isSetOperation) sortOut

    isSetTermF msetX sortOut = isOfHLevelRetractFromIso 2 (isoRepTermF (mtyp msetX) sortOut) (isSetRepTermF msetX sortOut)

    -- components of TermF as a functor
    {-# TERMINATING #-}
    mapTermF : ∀ {X Y} → (X →M Y) → (TermF X →M TermF Y)
    mapTermF f sort (varF' x) = varF' (f sort x)
    mapTermF f sort (join1F' t) = join1F' (mapTerm1 (mapTermF f) sort t)

    {-# TERMINATING #-}
    mapTermF-id : ∀ {X} → mapTermF (idfunM X) ≡ idfunM (TermF X)
    mapTermF-id {X} i sort (varF' x) = varF' x
    mapTermF-id {X} i sort (join1F' t) = (
        join1F' (mapTerm1 (mapTermF (idfunM X)) sort t)
          ≡⟨ cong join1F' ((cong mapTerm1 mapTermF-id ≡$ sort) ≡$ t) ⟩
        join1F' (mapTerm1 (idfunM (TermF X)) sort t)
          ≡⟨ cong join1F' ((mapTerm1-id ≡$ sort) ≡$ t) ⟩
        join1F' t ∎
      ) i

    {-# TERMINATING #-}
    mapTermF-∘ : ∀ {X Y Z : MType} → (g : Y →M Z) → (f : X →M Y) →
      mapTermF (g ∘M f) ≡ mapTermF g ∘M mapTermF f
    mapTermF-∘ g f i sort (varF' x) = varF' (g sort (f sort x))
    mapTermF-∘ g f i sort (join1F' t) = (
        join1F' (mapTerm1 (mapTermF (g ∘M f)) sort t)
          ≡⟨ cong join1F' ((cong mapTerm1 (mapTermF-∘ g f) ≡$ sort) ≡$ t) ⟩
        join1F' (mapTerm1 (mapTermF g ∘M mapTermF f) sort t)
          ≡⟨ cong join1F' ((mapTerm1-∘ (mapTermF g) (mapTermF f) ≡$ sort) ≡$ t) ⟩
        join1F' ((mapTerm1 (mapTermF g) ∘M mapTerm1 (mapTermF f)) sort t) ∎
      ) i

    -- TermF as a functor on catMSet
    ftrTermF : Functor catMSet catMSet
    F-ob ftrTermF = msetTermF
    F-hom ftrTermF = mapTermF
    F-id ftrTermF = mapTermF-id
    F-seq ftrTermF f g = mapTermF-∘ g f

    -- components of TermF as a monad

    pureTermF : ∀ {X} → (X →M TermF X)
    pureTermF sort = varF'

    ηTermF : NatTrans (ftrId catMSet) ftrTermF
    N-ob ηTermF msetX sortOut = varF'
    N-hom ηTermF {msetX} {msetY} f = refl

    {-# TERMINATING #-}
    joinTermF : ∀ {X} sort → TermF (TermF X) sort → TermF X sort
    joinTermF sort (varF' t) = t
    joinTermF sort (join1F' t) = join1F' (mapTerm1 joinTermF sort t)

    {-# TERMINATING #-}
    joinTermF-nat : ∀ {X Y : MType} f sort → (t : TermF (TermF X) sort)
      → joinTermF {X = Y} sort (mapTermF (mapTermF f) sort t) ≡ mapTermF f sort (joinTermF sort t)
    joinTermF-nat f sort (varF' t) = refl
    joinTermF-nat f sort (join1F' t) = cong join1F' (((
        (λ sort → mapTerm1 joinTermF sort ∘ mapTerm1 (mapTermF (mapTermF f)) sort)
          ≡⟨ sym (mapTerm1-∘ joinTermF (mapTermF (mapTermF f))) ⟩
        mapTerm1 (λ sort₁ → joinTermF sort₁ ∘ mapTermF (mapTermF f) sort₁)
          ≡⟨ cong mapTerm1 (funExt λ sort → funExt λ t → joinTermF-nat f sort t) ⟩
        mapTerm1 (λ x x₁ → mapTermF f x (joinTermF x x₁))
          ≡⟨ mapTerm1-∘ (mapTermF f) joinTermF ⟩
        (λ sort → mapTerm1 (mapTermF f) sort ∘ mapTerm1 joinTermF sort) ∎
      ) ≡$ sort) ≡$ t)

    μTermF : NatTrans (funcComp ftrTermF ftrTermF) ftrTermF
    N-ob μTermF msetX = joinTermF
    N-hom μTermF {msetX} {msetY} f = funExt λ sort → funExt λ t → joinTermF-nat f sort t

    open IsMonad

    -- TermF is a monad
    {-# TERMINATING #-}
    ismonadTermF : IsMonad ftrTermF
    η ismonadTermF = ηTermF
    μ ismonadTermF = μTermF
    idl-μ ismonadTermF = makeNatTransPathP (λ i → F-rUnit i) (λ i → ftrTermF) refl
    idr-μ ismonadTermF = makeNatTransPathP (λ i → F-lUnit i) (λ i → ftrTermF) lemma
      where lemma : (λ msetX sort t → joinTermF sort (mapTermF (λ sortOut → varF') sort t)) ≡
                    (λ msetX sort t → t)
            lemma i msetX sort (varF' x) = varF' x
            lemma i msetX sort (join1F' t) = cong join1F' (((
                (λ sort' → mapTerm1 joinTermF sort' ∘ mapTerm1 (mapTermF pureTermF) sort')
                  ≡⟨ sym (mapTerm1-∘ joinTermF (mapTermF pureTermF)) ⟩
                mapTerm1 (λ sort₁ → joinTermF sort₁ ∘ mapTermF pureTermF sort₁)
                  ≡⟨ cong mapTerm1 (lemma ≡$ msetX) ⟩
                mapTerm1 (λ a x → x)
                  ≡⟨ mapTerm1-id ⟩
                (λ sort' t → t) ∎
              ) ≡$ sort) ≡$ t) i
    assoc-μ ismonadTermF = makeNatTransPathP (λ i → F-assoc i) (λ i → ftrTermF) lemma
      where lemma : (λ msetX sort t → joinTermF sort (mapTermF joinTermF sort t)) ≡
                    (λ msetX sort t → joinTermF sort (joinTermF sort t))
            lemma i msetX sort (varF' ttx) = joinTermF sort ttx
            lemma i msetX sort (join1F' t) = cong join1F' (((
                (λ sort' → mapTerm1 joinTermF sort' ∘ mapTerm1 (mapTermF joinTermF) sort')
                  ≡⟨ sym (mapTerm1-∘ joinTermF (mapTermF joinTermF)) ⟩
                mapTerm1 (λ sort₁ → joinTermF sort₁ ∘ mapTermF joinTermF sort₁)
                  ≡⟨ cong mapTerm1 (lemma ≡$ msetX) ⟩
                mapTerm1 (λ a x → joinTermF a (joinTermF a x))
                  ≡⟨ mapTerm1-∘ joinTermF joinTermF ⟩
                (λ sort' → mapTerm1 joinTermF sort' ∘ mapTerm1 joinTermF sort') ∎
              ) ≡$ sort) ≡$ t) i
            --join1F' (term1 o λ p → lemma i msetX (arity o ! p) (args p))

    monadTermF : Monad catMSet
    monadTermF = ftrTermF , ismonadTermF

    SyntaxF : MType
    SyntaxF = TermF (mtyp msetEmpty)

    msetSyntaxF : MSet
    msetSyntaxF = msetTermF msetEmpty

module _ {matsig : MatSignature} (fmat1 fmat2 : FreeMat matsig) where

  open MatSignature matsig
  open FreeMat
  open Term1
  open TermF

  {-# TERMINATING #-}
  opmapTermF : OpHom fmat1 fmat2 → ∀ {X} sort → TermF fmat1 X sort → TermF fmat2 X sort
  opmapTermF ophom sort (varF' x) = varF' x
  opmapTermF ophom sort (join1F' t) = join1F' (opmapTerm1 fmat1 fmat2 ophom sort (mapTerm1 fmat1 (opmapTermF ophom) sort t))
