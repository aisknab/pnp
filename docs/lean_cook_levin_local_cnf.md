# Finite local Cook–Levin CNF compiler

`PNP.Concrete.CookLevinLocalCNF` supplies the finite clause language used by
later tableau emitters.  Every source literal contains a `Fin width` index,
so the compiler cannot emit an out-of-range variable.

The layer proves:

- exact materialization and lookup of a width-sized Boolean assignment;
- literal, clause, and clause-list reflection into the concrete
  `CNFFormula` semantics;
- unit-clause reflection;
- exact finite implication clauses, including premise negation;
- pairwise exactly-one clauses and their full semantic equivalence;
- a three-constructor local constraint language for requirements,
  implications, and exactly-one groups;
- exact recursive clause counts for every constraint and program;
- `LocalProgram.toFormula_satisfied_iff` and
  `LocalProgram.toFormula_satisfiable_iff`; and
- `localProgram_formula_wellScoped`, proving every emitted literal index is
  below the formula's declared variable count.

The complete 75-declaration kernel audit has empty axiom closure.  This layer
does not enumerate a machine tableau, define initialization or transition
windows, produce a complete Cook–Levin formula, prove an emitter polynomial,
define a reduction, prove CNFSAT NP-complete or in P, or establish P = NP.
The concrete publication gate remains false.
