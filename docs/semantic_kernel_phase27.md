# Semantic kernel hardening — phase 27 (`TruthVec`)

## Purpose

Phases 1–26 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, finite-state `DPInd`, exact finite-graph `Hall`, finite lexicographic `RankInd`, least-failure `MinCounterexample`, exact affine `IntArith`, checked full/quotient `Transport`, and successor KImpl/KBundle/global boundaries that keep every legacy final theorem node quarantined.

Phase 27 implements the next primitive PCC-K rule family, `TruthVec`.

The rule evaluates an explicit bounded topological NAND program on the complete Boolean cube determined by its ordered input block. It independently computes every output bit, preserves input, assignment, and output order, and rejects caller-provided truth vectors, equality flags, completeness flags, normalization claims, solver responses, searches, optimizations, or oracle outputs.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`TruthVec` is a finite evaluator, not a Boolean-equivalence oracle over unbounded circuits.

A certificate supplies:

- an explicit bounded NAND program;
- an explicit ordered input block;
- explicit ordered output coordinates;
- the explicit complete Boolean-cube assignment domain.

The checker verifies that the supplied domain is exactly the canonical cube for the program inputs and then evaluates the program independently on every assignment. The caller does not supply the vector values or the claim that two vectors are equal.

The arity, program size, output count, vector-cell count, and total evaluation-step count are bounded before evaluation.

## Canonical program nodes

A program node is:

```text
SemanticTruthVecNode0(
  index,
  id,
  nodeKind,
  inputIds,
  value
)
```

Supported node kinds are:

```text
Input
Const
NAND
```

The checker requires:

- exact consecutive node indices;
- unique canonical node IDs;
- one initial contiguous input block;
- no input after a constant or NAND node;
- `Input` nodes with no dependencies and null stored value;
- `Const` nodes with no dependencies and an explicit Boolean value;
- `NAND` nodes with exactly two earlier node IDs and null stored value;
- no undeclared operator, precomputed result, vector, equality, solver, search, or oracle field.

The language is intentionally NAND-only apart from explicit Boolean constants and input coordinates. More convenient Boolean syntax must first compile to this canonical form.

## Ordered outputs

An output is:

```text
SemanticTruthVecOutput0(
  index,
  id,
  nodeId
)
```

Output indices are exact and consecutive. Output IDs are unique. Each output references a declared program node. Multiple output coordinates may read the same computed node, but the output-coordinate IDs and output order remain explicit.

The program record is:

```text
SemanticTruthVecProgram0(
  programId,
  nodes,
  outputs
)
```

It contains no domain-completeness, vector, equality, normalization, or external-evaluator assertion.

## Canonical Boolean-cube domain

An assignment is:

```text
SemanticTruthVecAssignment0(
  index,
  bits
)
```

A domain is:

```text
SemanticTruthVecDomain0(
  inputIds,
  assignments
)
```

For input order:

```text
x_0, x_1, ..., x_(n-1)
```

there must be exactly `2^n` assignments. The assignment at index `i` is the width-`n` binary representation of `i`, most-significant input first. For two inputs the required order is:

```text
00
01
10
11
```

The checker rejects:

- a missing or extra assignment;
- a repeated or skipped assignment index;
- a non-Boolean bit;
- a bit vector with the wrong arity;
- domain input IDs that differ from the program input block;
- any noncanonical assignment order.

The zero-input domain contains exactly one empty assignment.

## `TruthVec.evaluate`

A `TruthVec` proof node has payload:

```text
op   = evaluate
spec = SemanticTruthVecSpec0(...)
```

The operation is closed and accepts no proof premises. All finite computation inputs are contained in the checked program and domain.

For each assignment, the checker:

1. binds each input node from the assignment bit at the same input coordinate;
2. reads each explicit Boolean constant;
3. evaluates every NAND node from its two earlier Boolean values;
4. reads each ordered output coordinate;
5. stores the complete row in assignment order;
6. transposes the rows into one truth vector per output coordinate.

Every Boolean value is computed by the checker. No truth bit is accepted from the caller.

## Computed judgment

The accepted conclusion is exactly:

```text
SemanticTruthVecJudgment0(
  evaluationId,
  program,
  domain,
  inputIds,
  outputIds,
  assignmentCount,
  outputCount,
  rows,
  vectors,
  programDigest,
  domainDigest,
  vectorDigest,
  exactBooleanCubeDomain = true,
  exactInputArity = true,
  exactAssignmentOrder = true,
  topologicalNANDEvaluation = true,
  allAssignmentsEvaluated = true,
  everyOutputBitComputed = true,
  inputOrderPreserved = true,
  outputOrderPreserved = true,
  boundedEvaluation = true,
  noSolverSearchOptimizationOrOracleUsed = true,
  terminalJudgmentComputed = true
)
```

Each row contains the exact assignment and ordered output values. Each vector contains the exact ordered bits for one output coordinate. The supplied conclusion must be canonically identical to the computed judgment. Mutating one bit, coordinate, order, digest, count, domain, or audit flag rejects.

## Rule-family composition

`CheckSemanticKernelProofTruthVec0` validates a mixed proof DAG over:

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
IntArith
Transport
TruthVec
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofTransport0`;
2. every `TruthVec` node is checked in original proof-DAG order by exact bounded evaluation.

A predecessor rule that attempts to consume a `TruthVec` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
IntArith
Transport
TruthVec
```

`CheckSemanticKernelReadinessTruthVec0` removes `TruthVec` from the computed missing-rule list but continues to reject final-theorem readiness. One primitive family remains:

```text
FiniteRel
```

## Successor KImpl integration

`KImplSemanticTruthVecSuccessor0` composes the merged Transport successor boundary:

1. it filters the full proof DAG to the fourteen predecessor rule families;
2. it requires `CheckKImplTransportSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact Transport-era supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofTruthVec0`;
5. it computes readiness with `CheckSemanticKernelReadinessTruthVec0`;
6. it rejects final-theorem purpose while `FiniteRel` remains missing.

Caller readiness fields, stale Transport-only records, weakened TruthVec policies, and legacy structural failures reject.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-truthvec-semantic0.test.mjs \
  test/pcc-kimpl-truthvec-successor0.test.mjs
```

The tests cover:

- complete two-input NAND truth-vector evaluation;
- zero-input constant evaluation;
- input, assignment, and output ordering;
- incomplete and noncanonical domains;
- wrong assignment arity;
- late input nodes;
- forward NAND dependencies;
- unsupported operators;
- undeclared output nodes;
- caller vector, equality, and completeness assertions;
- premise rejection for closed finite computation;
- mutated vector rejection;
- explicit input-arity bounds;
- fail-closed rejection of predecessor rules consuming a TruthVec conclusion;
- development-only successor acceptance;
- final-purpose rejection with `FiniteRel` still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should consume `KImplSemanticTruthVecSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The final primitive rule after that integration is `FiniteRel`. It must evaluate explicit finite relations and compositions over canonical finite domains, enforce exact tuple arity and order, compute equality and composition independently, and reject caller-supplied closure, equality, completeness, solver, search, or oracle assertions.
