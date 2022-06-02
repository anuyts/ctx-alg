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
In `Cmat`, we define CMATs (contextual multisorted algebraic theories), as well as a few translations:
- The **cold** translation, which yields a free MAT with no substitution operations,
- The **warm** translation, which yields a free MAT with substitution operations, that can be extended with
  - an equational theory about substitution
  - the axioms of the source CMAT
Both translations have the same signature, and are indexed by a mode `m0`.
The idea is that the contexts of the resulting MAT will be the junctors from mode `m0`.

Note: there is currently still some code present that refers to a terminal mode `m\top`. I will probably remove this.

The setup is as follows:
- `Cmat.Signature` defines the signature of a CMAT presentation, consisting of:
  - a category of modes and junctors
  - a covariant presheaf of contexts (i.e. contexts at every mode, extensible with junctors)
    Edit: this covariant presheaf is now the Yoneda embedding of the chosen mode `m0`.
  - custom right-hand-sides (to which we add the native RHSs for substitutions and junctor morphisms)
    Edit: there is no longer a native RHS for substitutions.
    
  as well as the MAT signature of the **cold**/**warm** translation.
  
- `Cmat.Free.Presentation` defines the presentation of a free CMAT, which is almost a RHS-indexed container, only we get to specify a junctor for every argument of every operator. It also defines two translations:
  - The free MAT presentation of the **cold** translation.
  - The MAT presentation of the **hot** translation.
    This MAT is non-free: it's equational theory expresses that substitution respects identity and composition and commutes with all operators.

TBD
