# Semantic kernel hardening — phase 17 (`Hall`)

## Purpose

Phases 1–16 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, finite-state `DPInd`, and successor KImpl/KBundle/global gates that keep every legacy final theorem node quarantined.

Phase 17 implements the next primitive PCC-K rule family, `Hall`.

The report uses matching arguments inside finite routing and incidence constructions. A semantic Hall rule must decide the matching question for the displayed finite bipartite graph. It must not accept a caller-supplied `matchingComplete = true`, an unchecked matching list, a claimed deficient set, or a solver/oracle result.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`Hall` decides a combinatorial property of an explicit finite bipartite graph.

It does not infer why an application-specific pair should be an edge. The graph supplied to `Hall` is already the finite graph being analysed. Domain-specific edge semantics remain the responsibility of accepted derivations that construct or identify that graph, including future `FiniteRel`, `Transport`, and arithmetic rules.

The rule therefore proves one of two exact statements about its explicit graph:

```text
complete-matching
hall-deficient
```

The result is computed by the checker rather than imported as evidence.

## Explicit bipartite graphs

A graph is:

```text
SemanticHallGraph0(
  graphId,
  leftVertexIds,
  rightVertexIds,
  edges
)
```

Every edge is:

```text
SemanticHallEdge0(leftId, rightId)
```

The checker requires:

- a nonempty bounded left universe;
- a bounded right universe, which may be empty;
- canonical unique identifiers on each side;
- disjoint left and right identifier sets;
- a bounded edge array;
- canonical unique `(leftId, rightId)` edge order;
- every edge endpoint to belong to its declared side;
- no undeclared matching, deficiency, completion, solver, search, or oracle field.

Constructors canonicalize input for generator convenience, but the proof checker independently revalidates the complete graph shape.

## Deterministic maximum matching

`Hall.decide` computes a maximum matching from the canonical graph.

The implementation uses a deterministic layered augmenting-path procedure:

1. unmatched left vertices are scanned in canonical left order;
2. adjacency lists are scanned in canonical right order;
3. augmenting layers are built from the current unmatched left vertices;
4. deterministic depth-first augmentation is applied until no augmenting path remains.

The checker then verifies internally that every selected pair is a declared graph edge and that selected left and right endpoints are both injective.

If the matching saturates the left universe, the outcome is:

```text
complete-matching
```

and the computed matching is the terminal witness.

## Exact Hall-deficient witness

If the maximum matching does not saturate the left universe, the checker computes the canonical alternating-reachability witness:

- start from all unmatched left vertices;
- traverse unmatched edges from left to right;
- traverse matched edges from right to left;
- collect the reached left set `S`;
- recompute the exact graph neighbourhood `N(S)` from all declared edges.

Because the matching is maximum, no unmatched right vertex is reachable by this alternating search. The checker requires the reached right set to equal the independently recomputed exact neighbourhood.

It then verifies:

```text
S != empty
|N(S)| < |S|
```

and computes:

```text
deficiency = |S| - |N(S)|
```

The outcome is:

```text
hall-deficient
```

A caller cannot choose a different subset, omit a neighbour, enlarge the deficiency, or relabel a nonmaximum matching as a Hall witness.

## `Hall.decide`

A Hall proof node has payload:

```text
op    = decide
graph = SemanticHallGraph0(...)
```

`Hall.decide` takes no proof premises. Its conclusion is computed entirely from the explicit graph:

```text
SemanticHallJudgment0(
  graphId,
  outcome,
  leftVertexIds,
  rightVertexIds,
  leftCardinality,
  rightCardinality,
  edgeCount,
  matching,
  matchingSize,
  unmatchedLeftVertexIds,
  deficientLeftVertexIds,
  neighbourhoodRightVertexIds,
  deficiency,
  terminalJudgment,
  graphCanonical = true,
  maximumMatchingComputed = true,
  matchingEdgesValid = true,
  matchingInjective = true,
  exactNeighbourhoodComputed = true,
  leftComplete,
  hallDeficiencyVerified,
  decisionComputed = true
)
```

The supplied conclusion must be canonically identical to this computed result.

For a complete matching:

```text
leftComplete = true
hallDeficiencyVerified = false
deficiency = 0
```

For a deficient graph:

```text
leftComplete = false
hallDeficiencyVerified = true
deficiency > 0
```

## Rule-family composition

`CheckSemanticKernelProofHall0` validates a mixed proof DAG over:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
DPInd
Hall
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofDPInd0`;
2. every `Hall` node is checked in original proof-DAG order by recomputing the matching decision.

A predecessor rule that attempts to consume a `Hall` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Such consumption remains unavailable until an explicit semantic rule defines it.

## Readiness result

The executable primitive rule families are now:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
DPInd
Hall
```

`CheckSemanticKernelReadinessHall0` removes `Hall` from the computed missing-rule list but continues to reject final-theorem readiness. Six primitive families remain:

```text
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticHallSuccessor0` composes the merged DPInd successor boundary:

1. it filters the full proof DAG to the nine predecessor rule families;
2. it requires `CheckKImplDPIndSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact predecessor supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofHall0`;
5. it computes readiness with `CheckSemanticKernelReadinessHall0`;
6. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot supply semantic-ready booleans, missing-rule lists, final-emission flags, matching or deficiency assertions, or a weakened Hall policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-hall-semantic0.test.mjs \
  test/pcc-kimpl-hall-successor0.test.mjs
```

The tests cover:

- exact left-complete matching computation;
- exact Hall-deficient subset and neighbourhood computation;
- isolated-left-vertex deficiency;
- noncanonical vertex order rejection;
- duplicate and invalid-endpoint edge rejection;
- caller matching/completion assertion rejection;
- mutated matching and neighbourhood conclusion rejection;
- proof-premise rejection for `Hall.decide`;
- fail-closed rejection of predecessor rules consuming a Hall conclusion;
- development-only successor acceptance;
- final-purpose rejection with six primitive families still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should be updated to consume `KImplSemanticHallSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `RankInd`. It must bind an explicit well-founded rank domain, exact base-rank cases, accepted predecessor-rank invariants, strict rank decrease on every dependency, complete local case coverage, and an exact terminal rank-induction judgment.
