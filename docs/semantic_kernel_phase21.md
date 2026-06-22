# Semantic kernel hardening — phase 21 (`MinCounterexample`)

## Purpose

Phases 1–20 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, finite-state `DPInd`, exact finite-graph `Hall`, finite lexicographic `RankInd`, and successor KImpl/KBundle/global boundaries that keep every legacy final theorem node quarantined.

Phase 21 implements the next primitive PCC-K rule family, `MinCounterexample`.

The rule selects a least failing element from an explicit finite candidate domain. It does not trust caller fields such as `selectedCandidateId`, `least`, `minimal`, `complete`, `searchResult`, `solver`, or `oracle`. The checker derives the first failure from an ordered prefix of accepted local evidence: every earlier candidate has accepted hold evidence and the selected candidate has accepted failure evidence.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`MinCounterexample` is a structural least-element rule over an explicit finite ordered domain.

It does not establish the domain-specific meaning of “holds” or “fails.” Those judgments must already be accepted by predecessor semantic rules. The checker verifies only that:

- the candidate domain is explicit and finite;
- the candidate order is canonical;
- each earlier candidate carries accepted hold evidence;
- the selected candidate carries accepted failure evidence;
- the first accepted failure is computed from the evidence prefix;
- the terminal minimal-counterexample judgment is computed exactly.

Arithmetic comparison inside a property remains an obligation for `IntArith`. Relation semantics remain an obligation for `FiniteRel`. Cross-carrier and cross-mode movement remains an obligation for `Transport`.

## Candidate records

A candidate is:

```text
SemanticMinCandidate0(
  index,
  id,
  orderKey,
  holdsJudgment,
  failsJudgment
)
```

The checker requires:

- exact consecutive indices;
- canonical unique candidate identifiers;
- a nonnegative safe-integer order key;
- canonical `(orderKey, id)` order;
- predecessor semantic judgments for both the hold and failure alternatives;
- hold and failure judgments to be distinct;
- no caller status, selected, least, minimal, complete, solver, search, or oracle field.

Ties in `orderKey` are broken by canonical candidate ID order, so the domain has one deterministic total order.

## Explicit searches

A search is:

```text
SemanticMinCounterexampleSearch0(
  searchId,
  candidates,
  terminalCoordinate
)
```

The candidate array must be nonempty and bounded. The search record accepts only its declared structural fields. It cannot contain a selected candidate, a minimality flag, a precomputed search result, or an oracle certificate.

## Local evidence

For candidate `x` in search `S`, the only accepted evidence record types are:

```text
MinCounterexampleEvidence0.<S>.<x>.holds
MinCounterexampleEvidence0.<S>.<x>.fails
```

Each record contains exactly one field:

```text
holds = candidate.holdsJudgment
```

or:

```text
fails = candidate.failsJudgment
```

Every local evidence record must be an earlier accepted `Record.intro` node. Therefore the hold or failure judgment is backed by an accepted predecessor semantic proof node; a raw boolean or caller status is not evidence.

## `MinCounterexample.select`

A proof node has payload:

```text
op     = select
search = SemanticMinCounterexampleSearch0(...)
```

The payload does not name the selected candidate.

The proof premises form a nonempty canonical evidence prefix. For candidate positions `0, ..., k - 1`, the premises must be exact hold-evidence records. Position `k` must be an exact failure-evidence record and must be the final premise. No evidence after the first failure is accepted.

The checker therefore computes:

```text
selectedCandidate = candidates[k]
```

and constructs:

```text
SemanticMinCounterexampleJudgment0(
  searchId,
  candidateOrder,
  orderKeys,
  candidateCount,
  selectedCandidateId,
  selectedCandidateIndex,
  selectedOrderKey,
  terminalCoordinate,
  earlierCandidateIds,
  holdsEvidenceProofIds,
  failureEvidenceProofId,
  evidenceProofIds,
  evidenceRecords,
  terminalJudgment,
  explicitFiniteCandidateDomain = true,
  canonicalCandidateOrder = true,
  earlierCandidatesSatisfy = true,
  selectedCandidateFails = true,
  leastFailureComputed = true,
  evidencePrefixComplete = true,
  noSearchSolverOrOracleUsed = true,
  terminalJudgmentComputed = true
)
```

The terminal result is:

```text
SemanticMinimalCounterexampleResultJudgment0(
  searchId,
  candidateId,
  candidateIndex,
  orderKey,
  coordinate,
  failureJudgment
)
```

The supplied conclusion must be canonically identical to the computed result.

## Rejected forms

The checker rejects:

- noncanonical candidate order;
- duplicate IDs or nonconsecutive indices;
- identical hold and failure judgments;
- missing earlier evidence;
- evidence supplied out of candidate order;
- an all-holds prefix with no failure;
- evidence after the first failure;
- substituted hold or failure judgments;
- non-`Record.intro` evidence;
- caller-supplied selected, least, minimal, complete, solver, search, or oracle fields;
- a mutated terminal minimal-counterexample conclusion.

## Rule-family composition

`CheckSemanticKernelProofMinCounterexample0` validates a mixed proof DAG over:

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
MinCounterexample
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofRankInd0`;
2. every `MinCounterexample` node is checked in original proof-DAG order against earlier accepted evidence records.

A predecessor rule that attempts to consume a `MinCounterexample` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
MinCounterexample
```

`CheckSemanticKernelReadinessMinCounterexample0` removes `MinCounterexample` from the computed missing-rule list but continues to reject final-theorem readiness. Four primitive families remain:

```text
IntArith
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticMinCounterexampleSuccessor0` composes the merged RankInd successor boundary:

1. it filters the full proof DAG to the eleven predecessor rule families;
2. it requires `CheckKImplRankIndSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact RankInd-era supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofMinCounterexample0`;
5. it computes readiness with `CheckSemanticKernelReadinessMinCounterexample0`;
6. it rejects final-theorem purpose while any primitive family remains missing.

Caller readiness fields, stale RankInd-only records, weakened minimality policies, and legacy structural failures reject.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-mincounterexample-semantic0.test.mjs \
  test/pcc-kimpl-mincounterexample-successor0.test.mjs
```

The tests cover:

- least-failure selection after accepted hold evidence;
- failure at the first candidate;
- canonical candidate ordering;
- distinct hold and failure judgments;
- omission and reordering of earlier evidence;
- all-holds rejection;
- rejection of evidence after first failure;
- substituted evidence rejection;
- caller-selected and caller-minimality assertion rejection;
- mutated terminal decision rejection;
- rejection of non-`Record.intro` evidence;
- fail-closed rejection of predecessor rules consuming a MinCounterexample conclusion;
- development-only successor acceptance;
- final-purpose rejection with four primitive families still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should consume `KImplSemanticMinCounterexampleSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `IntArith`. It must check explicit bounded integer expressions, exact evaluation, canonical comparison and Presburger-style certificates, overflow-safe arithmetic, and the absence of hidden optimization, minimization, solver, or oracle calls.
