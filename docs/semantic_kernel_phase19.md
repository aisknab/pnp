# Semantic kernel hardening — phase 19 (`RankInd`)

## Purpose

Phases 1–18 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, finite-state `DPInd`, exact finite-graph `Hall`, and successor KImpl/KBundle/global boundaries that keep every legacy final theorem node quarantined.

Phase 19 implements the next primitive PCC-K rule family, `RankInd`.

The report uses lexicographic rank arguments in normalization, residual descent, HN/BUD blocker closure, selector scheduling, and ZeroSlack reasoning. A semantic rank-induction rule must bind an explicit finite ranked domain, check the rank order itself, require accepted local invariant evidence, verify strict rank decrease on every dependency, cover every item exactly once, and compute the terminal invariant. It must not trust caller fields such as `wellFounded`, `rankComplete`, `inductionComplete`, or `terminalReady`.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`RankInd` is structural induction over an explicit finite dependency domain ordered by fixed-arity nonnegative lexicographic ranks.

It does not prove the domain-specific content of a local invariant. Each local invariant must already be an accepted equality, formula, or record judgment. `RankInd` checks only that those accepted judgments are assembled over the exact ranked dependency structure.

Arithmetic facts used inside an invariant remain obligations for future `IntArith`; relation semantics remain obligations for `FiniteRel`; cross-carrier or cross-mode transfer remains an obligation for `Transport`.

## Rank objects

A rank is:

```text
SemanticRank0(coordinates)
```

The checker requires:

- between 1 and 16 coordinates;
- every coordinate to be a nonnegative safe integer;
- one fixed coordinate count for the complete program;
- no caller-supplied comparison or well-foundedness assertion.

Ranks are compared lexicographically by the checker.

## Ranked items

A ranked item is:

```text
SemanticRankItem0(
  index,
  id,
  rank,
  predecessorIds,
  invariant
)
```

The item kind is computed from its dependency list:

```text
base   predecessorIds = []
step   predecessorIds != []
```

The checker requires:

- exact consecutive evaluation indices;
- canonical unique item IDs;
- canonical order by `(rank, id)`;
- a nonempty prefix of base items;
- every base item to have the exact zero rank;
- every step item to have a nonzero rank and at least one predecessor;
- unique predecessor IDs in evaluation order;
- every predecessor to be an earlier item;
- every predecessor rank to be strictly lexicographically smaller;
- each invariant to be an equality, formula, or record judgment.

Strict rank decrease over a finite explicit item set supplies the well-foundedness argument. No separate `wellFounded = true` field is accepted.

## Explicit rank programs

A program is:

```text
SemanticRankProgram0(
  programId,
  rankArity,
  items,
  terminalItemId,
  terminalCoordinate
)
```

The terminal item must be the final evaluation coordinate. Every declared item must lie in the reverse dependency closure of that terminal item. Dead ranked items cannot be counted as evidence for a terminal invariant they do not support.

The program accepts only its declared structural fields. Well-foundedness, completion, induction-complete, terminal-ready, solver, search, or oracle assertions are rejected.

## Local cases

For item `x` in program `P`, the local case record type is:

```text
RankIndCase0.<P>.<x>
```

It contains exactly:

```text
invariant
dep.<predecessor-id> ...
```

The `invariant` field is the exact invariant declared for the current item. Every dependency field is the exact invariant declared for that predecessor.

Each case must be an earlier accepted `Record.intro` node. Therefore the current invariant and every predecessor invariant are backed by accepted semantic proof nodes. A raw case object or completion flag is not evidence.

The checker rejects a wrong record type, a missing or extra dependency field, a substituted predecessor invariant, a non-`Record.intro` premise, or cases supplied out of item order.

## `RankInd.close`

A `RankInd` proof node has payload:

```text
op      = close
program = SemanticRankProgram0(...)
```

and exactly one case premise per ranked item in canonical evaluation order.

The checker computes:

```text
SemanticRankIndJudgment0(
  programId,
  rankArity,
  itemOrder,
  baseItemIds,
  stepItemIds,
  rankAssignments,
  dependencyMap,
  terminalItemId,
  terminalCoordinate,
  terminalInvariant,
  terminalJudgment,
  caseProofIds,
  cases,
  canonicalRankOrder = true,
  zeroRankBasePrefix = true,
  strictRankDecrease = true,
  predecessorCoverageComplete = true,
  localInvariantEvidenceExact = true,
  allItemsEvaluated = true,
  allItemsContributeToTerminal = true,
  finiteLexicographicOrderWellFounded = true,
  terminalInvariantComputed = true
)
```

The supplied conclusion must be canonically identical to this computed closure. A caller cannot mutate the terminal coordinate, terminal invariant, rank assignment, dependency map, case order, or any closure flag.

## Rule-family composition

`CheckSemanticKernelProofRankInd0` validates a mixed proof DAG over:

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
RankInd
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofHall0`;
2. every `RankInd` node is checked in original proof-DAG order against earlier accepted local cases.

A predecessor rule that attempts to consume a `RankInd` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
RankInd
```

`CheckSemanticKernelReadinessRankInd0` removes `RankInd` from the computed missing-rule list but continues to reject final-theorem readiness. Five primitive families remain:

```text
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticRankIndSuccessor0` composes the merged Hall successor boundary:

1. it filters the full proof DAG to the ten predecessor rule families;
2. it requires `CheckKImplHallSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact Hall-era supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofRankInd0`;
5. it computes readiness with `CheckSemanticKernelReadinessRankInd0`;
6. it rejects final-theorem purpose while any primitive family remains missing.

Caller readiness fields, stale Hall-only records, weakened rank policies, and legacy structural failures reject.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-rankind-semantic0.test.mjs \
  test/pcc-kimpl-rankind-successor0.test.mjs
```

The tests cover:

- accepted fixed-arity lexicographic rank closure;
- exact zero-rank base prefix;
- canonical equal-rank ID order;
- strict predecessor-rank decrease;
- earlier-item and predecessor-order enforcement;
- missing and substituted local dependency evidence;
- dead-item rejection;
- caller well-foundedness assertion rejection;
- swapped local cases;
- mutated terminal closure rejection;
- rejection of non-`Record.intro` cases;
- fail-closed rejection of predecessor rules consuming a RankInd conclusion;
- development-only successor acceptance;
- final-purpose rejection with five primitive families still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should consume `KImplSemanticRankIndSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `MinCounterexample`. It must bind an explicit finite candidate domain, compute the least counterexample under a checked order, require accepted evidence that every earlier candidate satisfies the property, require accepted failure evidence at the selected candidate, and reject caller-supplied minimality or `least = true` assertions.
