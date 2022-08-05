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
- The **hot** translation, which yields a free MAT with substitution operations, that can be extended with
   - an equational theory about substitution
   - the axioms of the source CMAT.

Both translations have the same signature, and are indexed by a CMAT foundation, which determines what are the contexts of the resulting language.

Different parts are added in different places. The following table gives a bit of an overview. It should be read as follows:

- The bold lines are titles,

- Under every bold line we list the operations added there,

- Operations from the left and from above (and from the upper-left) are also inherited,

- "Custom" stands for operations custom to the specific theory at hand.
  
  | **Custom**            | **CMAT**    | **Cold**         | **Hot**        |
  |:--------------------- |:----------- |:---------------- |:-------------- |
  | **Operations**        | **`fcmat`** | **`fmatCold`**   | **`fmatHot`**  |
  | Custom                | `id-jhom`   | `idsub`          |                |
  |                       |             | `gensub` =       | `gensub` =     |
  |                       | `comp-jhom` | `compsub`        | `tmsub`        |
  |                       | `whiskerL`  | `mixWhiskerL`    |                |
  |                       | `whiskerR`  | `mixWhiskerR`    |                |
  | **Equations**         |             | **`matCold`**    | **`matHot`**   |
  |                       |             |                  | `tmsub-inctx`  |
  |                       |             | `compsub-lunit`  |                |
  |                       |             | `compsub-runit`  | `tmsub-runit`  |
  |                       |             | `compsub-assoc`  | `tmsub-assoc`  |
  |                       |             | Mixed whiskering |                |
  |                       |             | except 1 law     |                |
  | **Equational theory** | **`cmat`**  |                  | **`matHotEq`** |
  | Custom                | Whiskering  |                  | 1 mixed wh law |

The setup is as follows:

- `Cmat.Signature` defines 
  
   - the signature of a CMAT presentation, consisting of:
      - a category of modes and junctors
      - a covariant presheaf of contexts (i.e. contexts at every mode, extensible with junctors)
      - custom right-hand-sides (to which we add the native RHSs for substitutions and junctor morphisms)
   - CMAT foundations, consisting of:
      - a covariant presheaf of contexts over the category of modes and junctors.
         - The translation is called **closed** in general,
         - The translation is called **open** if the presheaf of contexts is representable, meaning that junctors from the representing mode `m0` serve as contexts.
   - the common MAT signature `matsigClosed` of the **cold**/**hot** translation.

- `Cmat.Free.Presentation` defines the presentation of a free CMAT, which is almost a RHS-indexed container, only we get to specify a junctor for every argument of every operator. It also defines two translations:
  
   - The **cold** translation: `fmatCold`, `matColdCat`
   - The **hot** translation: `fmatHot`, `matHotTmsub`, `matHotCat`

TBD
