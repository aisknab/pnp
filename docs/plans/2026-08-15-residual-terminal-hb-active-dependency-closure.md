# Residual terminal HB active-dependency closure milestone

## Legacy anchor

The pinned manuscript's Section 15 proof of `HB.NegativeClosure` uses the
local no-outcome rule that every surviving active HN or BUD vertex must emit a
blocker edge to another active vertex.  The edge strictly decreases the
combined rank and tie-break measure, so a least active vertex cannot exist.
This milestone reconstructs that one dependency edge on top of the existing
checked total table and exact ten-coordinate rank order.

## Unbounded abstraction

The result ranges over every `rankCount`, arbitrary selector type, arbitrary
finite grouped BN6 family, and every total HN/BUD dependency function.  Small
three-rank examples are regression fixtures only; no fixed rank, selector, or
circuit coordinate appears in the theorem interface.

## Objective

Project HN and budget activity directly from the existing typed-realizer
environment.  Exhaustively check that every active node has an active
dependency in its own total table row, combine that scan with the existing
exact-rank table checker, and use well-founded induction to prove that every
supplied HN/BUD activity bit is false.  Compose the result with the checked
typed-realizer contract so the HN and budget bot branches are impossible.

## Exact theorem boundary

The central all-node conclusion is:

```text
table.checkNoOutcomeActiveClosure environment = true ->
forall node, environment.hbActive node = false
```

The canonical grouped-family composition returns:

```text
checked strict gain or faithful strictly lower-rank seed
and exact combined-checker validity
and all-node HN/BUD inactivity
and well-foundedness of the supplied dependency relation
```

The checker accepts no proof, silence, local-validity, well-foundedness, or
closure flag.  It computes every condition from the existing activity bits,
total dependency rows, and exact-rank map.

## Regression and hostile evidence

- Accept an all-inactive environment over a descending mixed HN/BUD table.
- Reject an active node whose listed dependency is inactive.
- Reject a finite descending active chain at its active base row.
- Demonstrate that a locally closed active cycle can pass the local scan but
  fails the independent exact-rank table check.
- Exercise the exact checker equivalences, all-node silence theorem,
  specialized HN and budget consequences, lower-seed result, and canonical
  typed-realizer composition.
- Audit all public declarations and reject truncated node scans, omitted
  dependency membership, bypassed rank checks, retained HN/BUD result branches,
  assumptions, fixed ranks, shortcuts, and theorem-name overclaims.

## Conservative claim boundary

The activity bits, dependency rows, finite-to-exact rank map, selector family,
faithfulness predicate, and realizer claims remain explicit inputs.  The local
checker verifies active-to-active closure of those supplied tables; it does
not derive blocker activity, blocker semantics, or semantic dependency
completeness from terminal candidates.  The result leaves a verified gain or
a faithful lower seed and therefore does not yet prove rank-complete selector
silence or the full `HB.NegativeClosure` theorem.

Downstream blockers remain selector faithfulness and compatibility, terminal
construction and semantic completeness of the activity/dependency tables,
gain exclusion in the ZeroSlack branch, lower-seed rank induction, complete
route silence, encoded-size and polynomial generation/runtime bounds,
unconditional ZeroSlack, PCCMin, SAT in P, project-assumption removal, and the
root theorem/axiom audit.

## Release gates

Run the focused Lean build, axiom transcript, regression, and hostile Node
audit first.  Then reconcile the compiled inventory, publication map, formal
status, canonical report, durable workflow, and all derived expectations.
Require the full remote suite, a focused draft PR, every normal check, manual
merge, and fresh exact-merge reproduction before the corresponding full-site
PNPLabs publication and production gates.
