# Algebraic theories with contexts, in cubical Agda

## Practical remarks

For now, we use agda v2.6.2.

For the cubical library, we have a submodule.
To clone, use
```
git clone --recurse-submodules
```

## General setup

### Multisorted algebraic theories
In `Mat`, we define MATs (multisorted algebraic theories).
- `Mat.Signature` defines the "signature" of a MAT presentation, which is just a set of sorts.
- `Mat.Free.Presentation` defines the presentation of a free MAT, which is a sort-indexed container, and the corresponding functor `Term1`.
- `Mat.Free.Term` defines the free monad `TermF`.
- `Mat.Free.Model` defines the isomorphic categories `catModel1` of algebras for `Term1` and `catModelF` of Eilenberg-Moore algebras for `TermF`.
- `Mat.Presentation` defines the presentation of a MAT, which is a free MAT equipped with an equational theory.
- `Mat.Term` defines the monad `TermQ`.
- `Mat.Model` defines the isomorphic categories
  - `catModel1Eq` of algebras for `Term1` that respect the equational theory,
  - `catModelFEq` of Eilenberg-Moore algebras for `TermF` that respect the equational theory,
  - `catModel` of Eilenberg-Moore algebras for `TermQ`.
  
### Contextual multisorted algebraic theories
In `Cmat`, we define CMATs (contextual multisorted algebraic theories).

TBD
