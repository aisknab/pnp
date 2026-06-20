# Semantic kernel hardening — phase 4 (`Record`)

## Purpose

Phases 1–3 added semantic `Eq`, typed capture-avoiding `Subst`, and a fail-closed successor `KImpl` readiness boundary. Phase 4 implements the next primitive rule family, `Record`, without changing the sealed `7072f8d` source/checker or artefact release.

The proof report lists `Record` among the sixteen primitive PCC-K rules. A rule name alone is not sufficient: the checker must verify exactly how record evidence is introduced and consumed.

## Record judgment

A semantic record judgment has one record type and a canonically ordered list of fields:

```text
SemanticRecordJudgment0(
  recordType,
  [SemanticRecordField0(name, judgment), ...]
)
```

The checker requires:

- a non-empty record-type name;
- field names in canonical lexical order;
- unique field names;
- no undeclared record or field properties;
- acyclic nested record judgments;
- a bounded nesting depth;
- complete canonical comparison of every embedded judgment.

A record is interpreted as named conjunction evidence: every field contains one already established semantic judgment.

## Implemented operations

### `Record.intro`

For canonical fields `f1, ..., fn`, introduction requires exactly `n` earlier accepted premises. The conclusion field judgment at position `i` must be canonically identical to premise conclusion `i`. The payload must declare exactly the conclusion record type and canonical field-name list.

This prevents a record field from being introduced by a boolean assertion or by merely naming a proof reference.

### `Record.project`

Projection requires exactly one earlier premise whose conclusion is a valid semantic record judgment. The requested record type and field name must exist, and the new conclusion must be canonically identical to the selected field judgment.

Projection cannot synthesize a stronger or different judgment.

## Composition with `Eq` and `Subst`

`CheckSemanticKernelProofRecord0` validates a mixed `Eq`/`Subst`/`Record` DAG in two stages:

1. the filtered `Eq`/`Subst` sub-DAG is accepted by `CheckSemanticKernelProof0`;
2. `Record` nodes are checked in the original earlier-premise order.

An `Eq` or `Subst` node that attempts to consume a record premise is rejected because the base semantic checker cannot resolve that dependency. This remains fail-closed until a future rule explicitly defines such cross-family consumption.

## Readiness result

The executable semantic rule set is now:

```text
Eq
Subst
Record
```

`CheckSemanticKernelReadinessRecord0` therefore removes `Record` from the missing-rule list but continues to reject final-theorem readiness. Thirteen primitive rule families remain:

```text
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
FiniteRel
```

## Successor KImpl integration

`KImplSemanticRecordSuccessor0` composes the phase-3 boundary rather than bypassing it:

1. it filters the full DAG to the `Eq`/`Subst` base;
2. it requires `CheckKImplSuccessor0` to accept that base only as `development-only`;
3. it validates the full DAG with `CheckSemanticKernelProofRecord0`;
4. it computes readiness with `CheckSemanticKernelReadinessRecord0`;
5. it rejects final-theorem purpose while any primitive rule is missing.

The input cannot provide readiness booleans, missing-rule lists, public-emission flags, or a weakened release policy. Those values are computed by the checkers.

## Verification

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-record-semantic0.test.mjs \
  test/pcc-kimpl-record-successor0.test.mjs
```

The tests cover:

- accepted canonical record introduction;
- accepted field projection;
- rejection of an unproved field;
- rejection of unsorted or duplicate fields;
- rejection of a missing projection field;
- rejection of undeclared payload/readiness assertions;
- fail-closed rejection of `Eq`/`Subst` consumption of record evidence;
- development-only successor acceptance;
- final-purpose rejection with thirteen rules still missing;
- preservation of the phase-3 and legacy KImpl boundaries.

## Next step

The next primitive implementation should be `DAGInd`, because the report relies on topological DAG reasoning for proof nodes, truth-vector evaluation, and multiple generated artefact layers. It must define an explicit finite DAG, a node-local invariant, checked base cases, predecessor-complete induction steps, and an exact conclusion over all nodes. Only after that handler is accepted should the successor KBundle and global proof DAG consume the extended readiness record.
