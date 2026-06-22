# Semantic kernel hardening — phase 25 (`Transport`)

## Purpose

Phases 1–24 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, finite-state `DPInd`, exact finite-graph `Hall`, finite lexicographic `RankInd`, least-failure `MinCounterexample`, exact affine `IntArith`, and successor KImpl/KBundle/global boundaries that keep every legacy final theorem node quarantined.

Phase 25 implements the next primitive PCC-K rule family, `Transport`.

The rule moves an explicit finite bundle of already accepted semantic facts between explicit carrier coordinates. It checks carrier mode, coordinate order, coordinate role, exact source evidence, projection loss, and full-lift evidence. It does not trust caller declarations such as `rolesPreserved`, `fullLiftComplete`, `lostCoordinates`, `constructiveFullUse`, or a precomputed target fact bundle.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`Transport` is a checked coordinate transport for accepted facts. It does not recursively rewrite arbitrary semantic judgments, and it does not infer a full-mode theorem from quotient equality.

Every transported fact is an already accepted predecessor semantic judgment wrapped by an accepted `Record.intro` fact record. The transport checker changes only the carrier-coordinate envelope. The fact judgment itself is copied exactly.

This gives three sound operations:

```text
rename   same-mode order-preserving role-preserving bijection
project  full-to-quotient order-preserving role-preserving restriction
lift     quotient-to-full embedding plus accepted evidence for every added coordinate
```

A projection result is comparison-only. A quotient result cannot justify constructive full-mode use. A lift is constructive only because every full-only target coordinate has separately accepted evidence.

## Explicit carrier coordinates

A coordinate is:

```text
SemanticTransportCoordinate0(
  index,
  id,
  role
)
```

Indices are exact consecutive coordinates. IDs are unique canonical identifiers. Supported roles are:

```text
boundary
interface
truth
relation
profile
origin
kernel
obligation
prefix
direction
saturation
budget
charge
payload
```

The fixed role vocabulary prevents a transport from silently reinterpreting, for example, an obligation fact as a charge fact or an interface fact as a profile fact.

A carrier is:

```text
SemanticTransportCarrier0(
  carrierId,
  mode,
  coordinates
)
```

with mode:

```text
full
quotient
```

Carrier coordinate arrays are explicit, nonempty, finite, bounded, and ordered by their exact indices.

## Transport maps

A map entry is:

```text
SemanticTransportMapEntry0(
  index,
  sourceCoordinateId,
  targetCoordinateId
)
```

A specification is:

```text
SemanticTransportSpec0(
  transportId,
  operation,
  sourceCarrier,
  targetCarrier,
  mapping
)
```

The checker requires:

- exact consecutive map-entry indices;
- declared source and target coordinates;
- injectivity on both sides;
- strict preservation of source and target coordinate order;
- exact preservation of coordinate roles;
- the mode relation required by the operation;
- no caller-supplied lost-coordinate, lift-completion, preservation, solver, search, or oracle assertions.

For `rename`, the map must be a bijection over both carriers and the modes must agree.

For `project`, the source must be full, the target quotient, and every quotient target coordinate must be mapped from the full source. Unmapped full coordinates are computed as the lost-coordinate list.

For `lift`, the source must be quotient, the target full, and every quotient source coordinate must be mapped into the full target. Unmapped full target coordinates are computed as the required lift-evidence list.

## Fact evidence

For carrier `L` and coordinate `x`, a fact record is:

```text
TransportFact0.<L>.<x>
```

with one field:

```text
fact = accepted predecessor semantic judgment
```

Every fact record must be an earlier accepted `Record.intro` node. Therefore the fact judgment is backed by an accepted predecessor proof node. Raw values, caller booleans, record labels without premises, and earlier `Transport` conclusions are not fact evidence.

## `Transport.rename`

Premises contain exactly one fact record for every source coordinate in source-carrier order.

The checker requires an order-preserving, role-preserving same-mode bijection and computes the target fact array in target-carrier order. Each target fact records:

```text
targetCoordinateId
sourceCoordinateId
evidenceProofId
judgment
```

The judgment is copied exactly from its accepted source fact record.

## `Transport.project`

Premises again contain every full source fact, including facts for coordinates that the quotient forgets. This prevents projection from hiding absent source evidence.

The checker computes:

```text
lostSourceCoordinateIds
```

from the unmapped full coordinates. The resulting judgment records:

```text
projectionComparisonOnly = true
quotientResultCannotJustifyFullUse = true
constructiveTargetUseAllowed = false
constructiveFullUseAllowed = false
```

These fields are checker outputs, not caller inputs.

## `Transport.lift`

Premises first contain every quotient source fact in source order. They then contain one full-carrier fact record for every target-only coordinate, in target-carrier order.

The checker computes:

```text
liftedTargetCoordinateIds
```

and rejects a missing, reordered, wrong-carrier, wrong-coordinate, non-`Record.intro`, or substituted lift fact.

An accepted lift records:

```text
fullLiftEvidenceComplete = true
constructiveTargetUseAllowed = true
constructiveFullUseAllowed = true
```

No full-only coordinate receives an implicit default.

## Computed judgment

The supplied conclusion must exactly equal the checker-computed:

```text
SemanticTransportJudgment0(
  transportId,
  operation,
  sourceCarrier,
  targetCarrier,
  mapping,
  sourceFactProofIds,
  liftFactProofIds,
  targetFacts,
  lostSourceCoordinateIds,
  liftedTargetCoordinateIds,
  sourceCarrierDigest,
  targetCarrierDigest,
  mappingDigest,
  sourceFactCount,
  targetFactCount,
  orderPreserved = true,
  rolesPreserved = true,
  exactSourceEvidenceCoverage = true,
  exactTargetFactCoverage = true,
  projectionComparisonOnly,
  quotientResultCannotJustifyFullUse,
  fullLiftEvidenceComplete,
  constructiveTargetUseAllowed,
  constructiveFullUseAllowed,
  noImplicitDefaults = true,
  terminalJudgmentComputed = true
)
```

Mutating any target fact, coordinate, proof ID, lost-coordinate list, lift list, digest, mode-firewall flag, or preservation flag rejects.

## Rule-family composition

`CheckSemanticKernelProofTransport0` validates a mixed proof DAG over:

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
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofIntArith0`;
2. every `Transport` node is checked in original proof-DAG order against earlier accepted `Record.intro` fact evidence.

A predecessor rule that attempts to consume a `Transport` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
```

`CheckSemanticKernelReadinessTransport0` removes `Transport` from the computed missing-rule list but continues to reject final-theorem readiness. Two primitive families remain:

```text
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticTransportSuccessor0` composes the merged IntArith successor boundary:

1. it filters the full proof DAG to the thirteen predecessor rule families;
2. it requires `CheckKImplIntArithSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact IntArith-era supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofTransport0`;
5. it computes readiness with `CheckSemanticKernelReadinessTransport0`;
6. it rejects final-theorem purpose while either remaining primitive family is missing.

Caller readiness fields, stale IntArith-only records, weakened transport policies, and legacy structural failures reject.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-transport-semantic0.test.mjs \
  test/pcc-kimpl-transport-successor0.test.mjs
```

The tests cover:

- same-mode ordered rename;
- full-to-quotient comparison-only projection;
- quotient-to-full lift with exact added-coordinate evidence;
- role-changing and order-changing maps;
- omitted and reordered source facts;
- omitted and wrong-carrier lift facts;
- illegal quotient-to-full projection syntax;
- caller lift-completion and preservation assertions;
- non-`Record.intro` evidence;
- mutated conclusions;
- fail-closed rejection of predecessor rules consuming a Transport conclusion;
- development-only successor acceptance;
- final-purpose rejection with `TruthVec` and `FiniteRel` still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should consume `KImplSemanticTransportSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `TruthVec`. It must evaluate explicit bounded Boolean vectors independently, preserve output order, require exact arity and assignment domains, compute every vector bit, and reject caller-supplied equality, completeness, solver, search, or oracle assertions.
