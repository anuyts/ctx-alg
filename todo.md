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
  - For each context (naturally) `TermF Cold => TermF Hot`
  - `TermF Cold (FreePsh X) ~= TermF Hot X`
- Quotiented presentation: equational theory w.r.t. hot translation
- Quotiented translation to equational theory on hot translation
  - Characterize warm models with equations. They consist of:
    - a model functor from `catModeJunctor` to `CategoriesInSetCategory`
    - a presheaf for every custom RHS
    - a functor from `(Coslice m0)^op \times catModeJunctor` to `CategoriesInSetCategory` for the `jhom` RHS
    - the above, partially applied to the initial coslice `(m0, id_m0)`, yields the model functor (so you can omit that one)
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
