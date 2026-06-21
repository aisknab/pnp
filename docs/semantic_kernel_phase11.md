# Semantic kernel hardening — phase 11 (`TraceInd`)

## Purpose

Phases 1–10 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, exact obligation lifecycle induction, successor KImpl boundaries, and successor KBundle/global gates that quarantine every legacy final theorem node.

Phase 11 implements the next primitive PCC-K rule family, `TraceInd`.

The report relies on trace induction for bounded NAND evaluation and for the locked-NAND trace-equivalence argument. A semantic trace rule must bind each source coordinate, verify each NAND node against already evaluated inputs, preserve topological order, and bind the declared output coordinate to the declared output node. It must not accept a list merely because it is called a trace or because a caller sets a completion flag.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`TraceInd` is a structural topological induction rule over accepted semantic equations. It does not yet evaluate all Boolean assignments and does not replace the future `TruthVec` primitive.

For every trace node, the following must already be accepted semantic judgments:

- the exact source or NAND equation;
- the node’s current value invariant;
- every earlier input-node invariant used by that node.

The local case must itself be accepted `Record.intro` evidence containing those judgments. `TraceInd` checks that the equations and dependency links are exact and complete; `TruthVec` and `FiniteRel` remain responsible for finite semantic evaluation and relation-level conclusions.

## Trace terms and node syntax

Trace values use the existing typed semantic term syntax:

```text
SemanticVar0
SemanticConst0
SemanticApp0
```

Every trace value has sort `Bool`.

A finite trace is:

```text
SemanticTrace0(
  traceId,
  nodes,
  outputNodeId,
  outputCoordinate,
  outputTerm
)
```

Each trace node is:

```text
SemanticTraceNode0(
  index,
  id,
  nodeKind,
  inputIds,
  sourceCoordinate,
  sourceTerm,
  valueTerm,
  equation,
  invariant
)
```

The permitted node kinds are:

```text
Source
NAND
```

## Source nodes

A source node has no input trace nodes. Its `sourceCoordinate` is a canonical identifier and its source term must be a semantic variable or constant whose name is exactly that coordinate.

The checker requires:

```text
valueTerm = sourceTerm
equation = (valueTerm = sourceTerm)
invariant = (valueTerm = valueTerm)
```

Thus a source cannot silently rename, negate, project, or replace the declared source coordinate.

## NAND nodes

A NAND node has exactly two ordered input IDs. Both must name earlier trace nodes. Duplicate inputs are permitted because NAND may consume the same earlier value twice; dependency evidence is required once for each distinct input node while the ordered gate equation retains both occurrences.

For earlier values `u` and `v`, the checker recomputes:

```text
expectedValue = nand(u, v)
```

and requires:

```text
valueTerm = expectedValue
equation = (valueTerm = expectedValue)
invariant = (valueTerm = valueTerm)
```

Input order is semantic. Reversing the two inputs changes the canonical term and rejects unless the terms are themselves canonically identical.

This establishes exact syntactic NAND-trace equations. It does not claim that an unchecked payload is a Boolean theorem.

## Topological trace plan

The checker requires:

- a nonempty bounded node array;
- consecutive indices beginning at zero;
- canonical unique node IDs;
- every NAND input to reference an earlier node;
- every source and node value to have `Bool` sort;
- no undeclared trace or trace-node properties;
- an output node that exists in the trace;
- a canonical output coordinate;
- `outputTerm` canonically identical to the declared output-node value.

The output coordinate is therefore an explicit structural binding, not an assertion-shaped boolean flag.

## Local trace cases

For trace node `v`, the local case record type is:

```text
TraceIndCase0.<traceId>.<nodeId>
```

Every case contains exactly:

```text
current
equation
dep.<input-node-id> ...
```

The dependency fields are the unique earlier input nodes required by the trace node.

The checker requires:

- the case premise to be an earlier accepted `Record.intro` node;
- `equation` to equal the exact equation recomputed from the trace plan;
- `current` to equal the exact declared value invariant;
- every dependency field to equal the invariant closed for that earlier node;
- no missing, duplicated, stale, substituted, or extra dependency field.

## `TraceInd.close`

A `TraceInd` proof node has payload:

```text
op = close
trace = SemanticTrace0(...)
```

and exactly one local case premise per trace node, in trace-node order.

The checker derives:

```text
SemanticTraceIndJudgment0(
  traceId,
  nodeOrder,
  sourceNodeIds,
  nandNodeIds,
  outputNodeId,
  outputCoordinate,
  outputTerm,
  caseProofIds,
  cases,
  allSourceBindingsExact = true,
  allNANDEquationsExact = true,
  allNodesEvaluated = true,
  outputCoordinateBound = true
)
```

Each case result records the exact node kind, ordered input IDs, source coordinate, value term, equation, and invariant. The supplied conclusion must be canonically identical to this computed object.

A caller cannot reorder cases, reverse a NAND gate, substitute an input invariant, change the output term, rebind the output coordinate, or claim a different terminal trace.

## Rule-family composition

`CheckSemanticKernelProofTraceInd0` validates a mixed proof DAG over:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofOblTopoInd0`;
2. every `TraceInd` node is checked in original proof-DAG order against earlier accepted case records.

A predecessor rule that attempts to consume a `TraceInd` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Such consumption remains unavailable until an explicit semantic rule defines it.

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
```

`CheckSemanticKernelReadinessTraceInd0` removes `TraceInd` from the computed missing-rule list but continues to reject final-theorem readiness. Nine primitive families remain:

```text
FiniteExhaust
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticTraceIndSuccessor0` composes the merged OblTopoInd successor boundary:

1. it filters the full proof DAG to the six predecessor rule families;
2. it requires `CheckKImplOblTopoIndSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact predecessor supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofTraceInd0`;
5. it computes readiness with `CheckSemanticKernelReadinessTraceInd0`;
6. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot supply semantic-ready booleans, missing-rule lists, final-emission flags, or a weakened trace policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-traceind-semantic0.test.mjs \
  test/pcc-kimpl-traceind-successor0.test.mjs
```

The tests cover:

- accepted source and multi-gate NAND closure;
- exact ordered NAND equations;
- exact source-coordinate binding;
- topological input enforcement;
- rejection of a reversed NAND value;
- rejection of a forward input reference;
- rejection of missing or substituted input invariants;
- rejection of swapped local cases;
- rejection of an output term not equal to the output node;
- rejection of a mutated terminal output-coordinate binding;
- rejection of non-`Record.intro` local evidence;
- fail-closed rejection of predecessor rules consuming a `TraceInd` conclusion;
- development-only successor acceptance;
- final-purpose rejection with nine primitive families still missing;
- caller readiness, stale predecessor, and policy-weakening rejection;
- preservation of OblTopoInd-successor and legacy KImpl gates.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should be updated to consume `KImplSemanticTraceIndSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `FiniteExhaust`. It must validate an explicit finite domain, canonical complete enumeration, accepted per-element cases, absence of duplicates or omissions, and an exact universal conclusion without treating a finite-domain assertion as its own proof.
