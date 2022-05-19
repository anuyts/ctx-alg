# MATs
- Don't use Everything
- allow sorts and arities to be groupoids
- Example MAT
- Use dependent lists after all!
- Use Arity for axioms (obligatorily?) -> I don't think this is a good idea
- Lower priority
  - CwFs
  - CwF structure of EM-category
  - fold in cubical library?
  - elim (in cubical library?)

# CMATs

- Signature
- Free CMAT
  - Try to define warm/cold translations at once via a boolean parameter.
  - Open translation which uses junctors instead of contexts, and junctor morphisms instead of substitutions; with substitution
    - Note: you can pop a junctor from the context and whisker it with a junctor morphism:
      
      ```
      F |- |- θ : G => H
      -------------------------- whisker
      |- F * θ : F * G => F * H
      ```
      
      You cannot unwhisker however.
    - Note: in the open translation, the identity substitution is ill-typed, so you cannot mention variables. This is precisely the point!
    - Note: Open translates CMATs to CMATs:
      - its contexts are junctors
      - its `CustomRHS`s are the original `RHS`s, so its `RHS`s are the original `RHS`s plus junctors
      - it has no additional operators! Junctor substitutions are added by the CMAT operators.
  - Closed translation without substitution (call this crisp/cold/dead/solid)
  - Closed translation with substitution (call this hot/warm/live/liquid/fluid)
    - Note: applying a junctor to a substitution, takes a delayed substitution
- Proofs about this
  - For each context (naturally) `TermF Open => TermF ClosedSubst`
  - `TermF ClosedNoSubst (AddSubst X) ~= TermF ClosedSubst`
  - `AddSubst Empty ~= Empty`
  - `SyntaxF ClosedNoSubst ~= SyntaxF ClosedSubst`
  - Characterize models via adjoint functors (so you don't need to worry about contexts, types and junctors/junctor morphisms having or not having an intermediate representation)
- Quotiented presentation: equational theory w.r.t. `TermF` Open
- Quotiented translation to equational theory on `ClosedSubst` (or `Open`)
  - Characterize models via adjoint functors
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
- Non-instances
  - adjoint logic, LSR (no left adjoints)
  - linear TT (because junctors don't live in a context, so it's not well-typed to remove something from it)

# SOMATs

- Just to subsume AACMM21 and FSz22

# Running example

Via a commutative triangle SOMAT -> CMAT -> MAT, you can carry over and refine concepts from related work on SOMATs, by first giving the SOMAT concept & translation, then the CMAT concept and translation, then the SOMAT -> CMAT translation.
