# Residual terminal HB dependency-table closure milestone

## Objective

Replace the independently supplied HB edge list with one total data-only
dependency table over every finite HN and budget node.  Materialize the graph
mechanically from that table, check every row dependency against the existing
exact ten-coordinate residual rank, and derive exact table-to-edge coverage,
well-founded induction, and absence of circular dependency chains.

## Why this milestone is next

The checked HB blocker-graph acyclicity contract proves strict descent only for
edges already present in a supplied list.  It deliberately leaves open whether
the finite HB domain has a row for every HN and budget node and whether the
graph contains every dependency named by those rows.  A total dependency
function removes both finite representation omissions without asserting that
the caller supplied the manuscript's semantically correct dependencies.

## Checked interface

1. Enumerate every HN and budget node at every index of the arbitrary finite
   rank carrier and prove exact membership in that enumeration.
2. Define a total data-only table assigning a finite dependency list to every
   enumerated node, together with the existing finite-to-exact rank map.
3. Materialize the dependency graph from every table row.  Do not accept a
   second caller-supplied edge list or any proof, readiness, closure, or silence
   field.
4. Exhaustively check the finite-to-exact rank embedding and every dependency
   in every row for strict exact-rank descent.
5. Prove that checker acceptance is equivalent to the exact table proposition
   and that a materialized graph edge occurs exactly when the dependency occurs
   in the corresponding table row.
6. Derive exact-rank descent, accessibility, well-foundedness, no nonempty
   directed cycle, and well-founded induction for arbitrary predicates over the
   total supplied table.
7. Compose acceptance with the checked Packet typed-realizer table so every
   faithful gain or bot retains its existing proof-bearing meaning, every HN or
   budget bot names a row in the total table, and every lower seed descends in
   the exact rank.

## Regression and hostile evidence

- Accept a mixed HN/BUD table with base rows and successively descending mutual
  dependency forms.
- Reject a same-rank dependency, an upward dependency, and a two-node cycle.
- Exercise exact node enumeration, table-to-edge equivalence, checker
  equivalence, rank descent, accessibility, well-founded induction, no-cycle,
  and typed-realizer composition.
- Derive the axiom transcript from every declaration in the new module and
  reject unaudited declaration forms, proof-carrying input fields, weakened
  exhaustive scans, caller-supplied edge lists, and overclaiming documentation.

## Conservative claim boundary

The dependency table, finite-to-exact rank mapping, selector family,
faithfulness predicate, blocker activity tables, and realizer claims remain
explicit inputs.  Exact table coverage means only that every node in the
finite HN/BUD domain has a row and every dependency in that row becomes a graph
edge.  It does not prove that a row has the manuscript's blocker semantics,
that the supplied dependency list is complete relative to terminal data, or
that active blockers are false or silenced.  Generic well-founded induction
does not itself supply the local invariant premise.  This milestone therefore
does not establish selector compatibility, rank-complete selector silence, the
full `HB.NegativeClosure`, unconditional ZeroSlack, PCCMin, polynomial size or
runtime, SAT in P, removal of a project assumption, or P = NP.

## Release gates

Run the focused Lean axiom transcript and regression first, then the hostile
Node audit, inventory and publication regeneration checks, full repository
verification, and a fresh clean exact-commit reproduction.  Publish through a
focused draft PR, require every normal check, merge manually, and reproduce the
merge before the corresponding full-surface PNPLabs synchronization and
production gates.
