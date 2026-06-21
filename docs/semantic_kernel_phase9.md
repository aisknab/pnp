# Semantic kernel hardening — phase 9 (`OblTopoInd`)

## Purpose

Phases 1–8 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, successor KImpl boundaries, and successor KBundle/global gates that quarantine every legacy final theorem node.

Phase 9 implements the next primitive PCC-K rule family, `OblTopoInd`.

The proof report states that only rewrite family R5 creates obligations, only R6, R7, and R8 discharge them, R6 requires a full-mode cancellation witness, projected equality is insufficient for constructive full-mode discharge, and every final obligation ledger must contain no open obligation. A semantic obligation rule must enforce those lifecycle facts rather than accepting a list whose entries merely say `closed`.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`OblTopoInd` is a structural lifecycle rule. It does not manufacture the mathematical proof that a source, target, frontier, projection, rewrite, or discharge witness is correct.

Those objects must already be accepted semantic judgments. They are assembled into typed `Record.intro` evidence before `OblTopoInd` may use them.

The rule checks:

- exact creation coordinates;
- exact discharge coordinates;
- exact dependency-topological order;
- permitted creation and discharge rule families;
- mode consistency;
- full-mode witness presence;
- exact dependency invariants;
- exact terminal absence of open obligations.

Domain-specific correctness of R5–R8 evidence remains the responsibility of semantic rules that produce those accepted judgments, including future `Transport`, `TruthVec`, `FiniteRel`, and arithmetic rules.

## Typed creation evidence

For obligation `o` in plan `P`, creation evidence has record type:

```text
ObligationCreation0.<P>.<o>.<mode>
```

and exactly these canonical fields:

```text
frontier
projection
source
target
```

The plan records `creationRule = R5`. No other creation rule is accepted.

The creation record itself must be an earlier accepted `Record.intro` proof node, so every field must already be an accepted semantic judgment.

## Typed discharge evidence

Discharge evidence has record type:

```text
ObligationDischarge0.<P>.<o>.<rule>.<mode>
```

The permitted discharge rules are:

```text
R6
R7
R8
```

A quotient-mode discharge record contains exactly:

```text
result
```

A full-mode discharge record contains exactly:

```text
fullWitness
result
```

Additional mode restrictions are fail-closed:

- R6 may discharge only a `Full` obligation;
- every `Full` obligation requires an accepted `fullWitness` judgment;
- a `Quot` obligation may not claim a full-mode witness;
- the discharge record type must bind the exact plan, obligation, discharge rule, and mode.

This prevents projected evidence from being relabelled as a constructive full-mode discharge.

## Obligation plan

A finite obligation plan is:

```text
SemanticObligationPlan0(
  planId,
  [SemanticObligation0(...), ...]
)
```

Each obligation contains:

```text
id
mode
dependencies
createIndex
dischargeIndex
creationRule
dischargeRule
creationEvidence
dischargeEvidence
```

The checker requires:

- a nonempty bounded obligation set;
- canonical unique obligation IDs;
- canonical dependency lists with no duplicates;
- obligations in strictly increasing creation order;
- one creation and one discharge event per obligation;
- all event indices to form exactly `0, ..., 2n-1` with no gap or collision;
- creation before discharge;
- every dependency to be declared;
- every dependency created before its dependent obligation;
- every dependency discharged before its dependent obligation;
- dependency mode equality.

Cross-mode dependencies are rejected at this phase. A future explicit `Transport` derivation is required before a mode-changing dependency can be consumed.

## Local closure cases

Obligations are closed in discharge order. The local case record type is:

```text
OblTopoIndCase0.<planId>.<obligationId>
```

Every case contains exactly:

```text
closed
creation
discharge
dep.<dependency-id> ...
```

The case must itself be earlier accepted `Record.intro` evidence. The checker requires:

- `creation` to equal the exact declared R5 creation record;
- `discharge` to equal the exact declared R6/R7/R8 discharge record;
- `closed` to be an accepted semantic judgment object;
- every `dep.<id>` field to equal the invariant closed for that dependency earlier in discharge order;
- no missing, duplicate, stale, substituted, or extra dependency field.

## `OblTopoInd.close`

An `OblTopoInd` proof node has payload:

```text
op = close
plan = SemanticObligationPlan0(...)
```

and exactly one local case premise per obligation, in computed discharge order.

The checker derives:

```text
SemanticOblTopoIndJudgment0(
  planId,
  obligationOrder,
  dischargeOrder,
  eventOrder,
  sourceObligationIds,
  terminalObligationIds,
  fullModeObligationIds,
  quotientModeObligationIds,
  caseProofIds,
  cases,
  dischargedObligationIds,
  openObligationIds = [],
  allDependenciesClosed = true,
  fullModeDischargesVerified = true,
  allObligationsDischarged = true,
  noOpenObligations = true
)
```

The supplied conclusion must be canonically identical to this computed result. A caller cannot alter the event order, omit a dependency, swap cases, leave an open obligation, downgrade a full-mode discharge, or change the terminal closure.

## Rule-family composition

`CheckSemanticKernelProofOblTopoInd0` validates a mixed proof DAG over:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofLedgerInd0`;
2. every `OblTopoInd` node is checked in original proof-DAG order against earlier accepted case records.

A predecessor rule that attempts to consume an `OblTopoInd` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Such consumption remains unavailable until an explicit semantic rule defines it.

## Readiness result

The executable primitive rule families are now:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
```

`CheckSemanticKernelReadinessOblTopoInd0` removes `OblTopoInd` from the computed missing-rule list but continues to reject final-theorem readiness. Ten primitive families remain:

```text
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

`KImplSemanticOblTopoIndSuccessor0` composes the merged LedgerInd successor boundary:

1. it filters the full proof DAG to the five predecessor rule families;
2. it requires `CheckKImplLedgerIndSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact predecessor supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofOblTopoInd0`;
5. it computes readiness with `CheckSemanticKernelReadinessOblTopoInd0`;
6. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot supply semantic-ready booleans, missing-rule lists, final-emission flags, or a weakened lifecycle policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-obltopoind-semantic0.test.mjs \
  test/pcc-kimpl-obltopoind-successor0.test.mjs
```

The tests cover:

- accepted R5 creation with R6/R7/R8 discharge;
- exact interleaved creation/discharge event scheduling;
- exact source and terminal obligation computation;
- full-mode witness enforcement;
- rejection of quotient-mode R6 discharge;
- rejection of a substituted dependency invariant;
- rejection of missing dependency evidence;
- rejection of event gaps or collisions;
- rejection of swapped local cases;
- rejection of a mutated terminal open-obligation result;
- rejection of non-`Record.intro` local evidence;
- fail-closed rejection of predecessor rules consuming an `OblTopoInd` conclusion;
- development-only successor acceptance;
- final-purpose rejection with ten rule families still missing;
- caller readiness, stale predecessor, and policy-weakening rejection;
- preservation of LedgerInd-successor and legacy KImpl gates.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should be updated to consume `KImplSemanticOblTopoIndSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `TraceInd`. It must bind a finite topological computation trace, exact source and gate equations, accepted local transition evidence, output-coordinate identity, and an exact terminal trace theorem.
