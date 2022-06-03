# Cubical
- reflection for data types
- h-level of a homotopy co-end?

# MATs
- Lower priority
  - CwFs
  - CwF structure of EM-category
  - fold in cubical library?
  - elim (in cubical library?)

# CMATs
- MAT signature: OK
- Free CMAT: OK
- Proofs about this
  - `TermF fmatCold (FreePsh X) ~= TermF matHotTmsub X`
  - `TermF matColdCat (FreePsh X) ~= TermF matHotCat X`
- CMAT Presentation: equational theory w.r.t. hot translation
  - Note: you cannot use the terminal context, because a morphism `T.Φ -> T.Ψ` and a context `Γ` do not yield `Γ.Φ -> Γ.Ψ`.
- CMAT translation to equational theory on hot translation
  - Characterize hot models with equations. They consist of:
    - a model functor `ftrCatCtx : catModeJunctor -> catCatInSet`
      - non-skew: mapping out the objects yields `pshCtx : catModeJunctor -> catSet`
      - skew: a morphsim from `pshCtx`
    - a presheaf for every custom RHS
    - a functor `ftrCatJunctorClosed : (catGrothConstr ftrCatCtx)^op \times catModeJunctor -> catCatInSet` for the `jhom` RHS
      - non-skew: mapping out the objects factors over `fst : catGrothConstr ftrCatCtx -> catModeJunctor` as
        `HomFunctor : catModeJunctor^op \times catModeJunctor -> catSet`
      - skew: a morphism from `HomFunctor`
    - for every `Γ` a functor `ftrCatJunctorOpen : (catGrothConstr (ftrCatJunctorClosed(Γ,-)))^op \times catModeJunctor -> catCatInSet`
      - which factors over `catGrothConstr (ftrCatJunctorClosed(Γ,-)) -> catGrothConstr ftrCatCtx` as
        `ftrCatJunctorClosed`
    - (We can now generate a presheaf for every (non-custom) RHS)
    - a presheaf morphism for every operator
    - a commutative diagram of presheaf morphisms for every axiom
- General applications
  - Generic substitution
    - Note: generic renaming is not necessary first, because ctx extension is a junctor hence a functor.
  - Note: in order to do generic scope- & type-checking, generate untyped and typed Cmat from a Cmat whose types are a Mat (containing Ctx, Junctor and CustomRHS as sorts) and whose operators explicitly have a list of type-level arguments
  - Generic scope-checker (possible)
    - Generic raw syntax type (not possible)
  - Generic type-checker (not bidirectional, but allow type annotations)
    - Modes must be given
    - You need to give both CMATs (more-typed and lesser-typed)
    - You need to specify the type-level parameters missing on every lesser-typed term constructor
    - You need to explain how to insert these
  - Define renaming (required to implement functorial action of context extension on substitution)
  - Define substitution
  - presheaf models
- Instances
  - SOMATs
    - scope-check
    - subsume AACMM21 and FSz22
  - MTT with external mode theory
    - scope-check (ticks!)
    - type-check
    - prettyprint?
    - prove normalization?
  - dual context
    - prove normalization?
  - amazing right adjoint
    - prove normalization?
  - poplmark challenge 1
  - cbpv?
- Non-instances
  - adjoint logic, LSR (no left adjoints)
  - linear TT (because junctors don't live in a context, so it's not well-typed to remove something from it)

# SOMATs

- Just to subsume AACMM21 and FSz22

# Running example

Via a commutative triangle SOMAT -> CMAT -> MAT, you can carry over and refine concepts from related work on SOMATs, by first giving the SOMAT concept & translation, then the CMAT concept and translation, then the SOMAT -> CMAT translation.
