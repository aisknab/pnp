# Finite Cook–Levin tableau CNF semantics

`PNP.Concrete.CookLevinTableauCNFSemantics` proves a bidirectional semantic
theorem for the finite whole-tableau formula introduced by the preceding CNF
syntax layer.

The intrinsic semantic object is a function from every represented time to a
finite row. Each row contains one bounded state, one bounded head position,
and one tape symbol at every position in the explicit window. Its successor is
computed by the same first-match local action used by the emitted clauses;
halted and missing-rule states stutter exactly.

The principal results are:

- `VerifierTableauProblem.formula_satisfiable_iff_finiteAccepting`
- `VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_finiteAccepting`

Both directions are constructive at the data level. A satisfying assignment
is decoded by finite first-true searches. Conversely, a finite accepting
tableau generates an assignment of exactly `FormulaWidth` bits. The proof
covers all one-hot rows, exact input-only and paired-certificate initial rows,
every state/head/write implication, every untouched-cell implication, and the
designated final accepting state.

The complete audit prints all 161 explicit declarations. Their closures use
only `propext` and `Quot.sound` where Lean's list-membership and function
extensionality library lemmas require them; no project axiom or
`Classical.choice` occurs.

## Exact boundary

This milestone proves equivalence with the intrinsic finite-row transition
system. It does not yet prove that the finite window simulates the focused raw
`Tape` zipper, so it does not yet establish equivalence with
`boundedDecide`, a polynomial reduction, CNF-SAT NP-completeness, CNF-SAT in
P, or P = NP. The concrete publication gate remains false.
