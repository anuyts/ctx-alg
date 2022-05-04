Insights:
- d0cde78 define `Term` like `TermF` but with
  - axioms
  - a constructor for `joinTermFTerm`
  - laws relating `joinTermFTerm` to `ast` and `var`
  I think this works except that Agda's termination checker balks at functors
- 7d898a9 define `Term` like `TermF` but with axioms: almost but you get screwed by implicit arguments.
- 3fd6746 quotienting out `TermF`: you can't have `Term1 Term -> Term`
- 3e789ef constructors
  - `term : TermF -> Term`
  - `ast : Term1 Term -> Term`
  - axioms only for `TermF TermF`
  `joinTerm` cannot be proven for `byAxiom`.
