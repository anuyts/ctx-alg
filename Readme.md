# Algebraic theories with contexts, in cubical Agda

## Practical remarks

For now, we use agda v2.6.2.

For the cubical library, we have a submodule.
To clone, use

```
git clone --recurse-submodules
```

## Further reading
See related links on [my homepage](https://anuyts.github.io/).

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

- The **settling** translation translates CMATs to MATs. It comes in two flavours:
  
   - The **cold** translation, which translates a free CMAT to a MAT with no substitution operations other than substitution composition,
   - The **hot** translation, which translates a free CMAT to a MAT with substitution operations.
     It extends to a translation from non-free CMATs to MATs.
  
  Both flavours have the same signature, and are indexed by a CMAT foundation, which determines what are the contexts of the resulting language.

- The **levitating** translation is actually a special case of the **settling** translations, which is indexed by a mode `m0`.
  To levitate a CMAT is to settle it on the foundation whose contexts at mode `m` are really junctors from `m0` to `m`.

Different parts are added in different places. The following table gives a bit of an overview. It should be read as follows:

- The bold lines are titles,

- Under every bold line we list the operations added there,

- Operations from the left and from above (and from the upper-left) are also inherited,

- "Custom" stands for operations custom to the specific theory at hand.
  
  | **Custom**            | **CMAT**      | **Cold**            | **Hot**             |
  |:--------------------- |:------------- |:------------------- |:------------------- |
  | **Signature**         | **`cmatsig`** | **`matsigSettled`** | **`matsigSettled`** |
  | **Operations**        | **`fcmat`**   | **`fmatCold`**      | **`fmatHot`**       |
  | Custom                | `id-jhom`     | `idsub`             |                     |
  |                       |               | `gensub` =          | `gensub` =          |
  |                       | `comp-jhom`   | `compsub`           | `tmsub`             |
  |                       | `whiskerL`    | `mixWhiskerL`       |                     |
  |                       | `whiskerR`    | `mixWhiskerR`       |                     |
  | **Equations**         |               | **`matCold`**       | **`matHot`**        |
  |                       |               |                     | `tmsub-inctx`       |
  |                       |               | `compsub-lunit`     |                     |
  |                       |               | `compsub-runit`     | `tmsub-runit`       |
  |                       |               | `compsub-assoc`     | `tmsub-assoc`       |
  |                       |               | Mixed whiskering    |                     |
  |                       |               | except 1 law        |                     |
  | **Equational theory** | **`cmat`**    |                     | **`matHotEq`**      |
  | Custom                | Whiskering    |                     | 1 mixed wh law      |

The setup is as follows:

- `Cmat.Signature` defines 
  
   - the signature of a CMAT presentation, consisting of:
      - a category of modes and junctors
      - custom right-hand-sides (to which we add the native RHSs for substitutions and junctor morphisms)
   - CMAT foundations, consisting of:
      - a covariant presheaf of contexts over the category of modes and junctors.
         - The translation is called **settled** in general,
         - The translation is called **levitated** if the presheaf of contexts is representable, meaning that junctors from the representing mode `m0` serve as contexts.
   - the common MAT signature `matsigSettled` of the **cold**/**hot** translation.

- `Cmat.Free.Presentation` defines the presentation of a free CMAT, which is almost a RHS-indexed container, only we get to specify a junctor for every argument of every operator.
   It also defines the settling translation, indexed by a "temperature" (hot/cold):
  
   - The general **settling** translation: `fmatSettled`, `matSettled`
   - The **cold** translation: `fmatCold`, `matCold`
   - The **hot** translation: `fmatHot`, `matHot`

TBD
