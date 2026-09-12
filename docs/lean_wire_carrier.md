# Computed wire-backed carrier transport

M250 reconstructs the computational-value preservation edge in sections 2, 4
and 5 of the manuscript pinned by
[the archive manifest](../archive/legacy-v0/ARCHIVE.json).

## Actual fields and complete observations

A `WireCarrier inputs outputs fields` contains an actual implementation and an
ordered tuple `Fin fields → Source inputs implementation.gateCount`. Each field
reads an actual primary input, constant or NAND gate under the input valuation.
There is no arbitrary profile observer, supplied truth function or proof-only
Boolean source.

The ordinary output tuple is followed by every field source for the duration of
the physical transformation. This adds no NAND gate. Exact pack/unpack identities
retain the program and the complete ordered source tuple, not merely their
lengths. After transformation, ordinary outputs and rebound fields are recovered
with their original separate dimensions.

The wire bindings are actual input data. Representing these computational values
does not derive every manuscript record, role or history. Proof-only records do
not become Boolean sources.

## Computed normalization and literal replacement

Normalization runs the existing constant-propagation, sharing and output-cone
pruning closure on all the combined observations. For every finite dimension,
input valuation, ordinary output and field, the result preserves the original
value. Exact trace savings account for physical NAND gates. The combined result
is quiet for all three passes, and normalization is idempotent.

A field producer cannot be pruned merely because no ordinary output uses it.
Every selected field producer is an actual computed support-interface port.

The actual arbitrary-support compiler uses the combined program, extracted
boundary, complete interface and replacement word. No observer, wire map,
topological order or successful result is supplied to the constructor.
The local open-function equality includes every computed field port; it is not
a certificate of whole-circuit correctness. Under that equality, a successful
literal splice preserves every ordinary output and every field value.
Exterior and replacement gates are counted exactly, including larger
replacements. A strict local saving gives a strict whole-program saving.

Equal local Boolean functions do not guarantee acyclic literal wiring.
The actual compiler rejects a cyclic rebinding even when the local replacement
has the required open function. For production predecessor closure, acyclicity
and successful compilation are derived from the actual combined program.
These wire-backed fields are already physical observations, so that particular
specialization needs no additional abstract profile coordinates. It does not
assert that the complete manuscript profile is empty.

## Remaining mathematical obligations

The complete manuscript carrier and noncomputational record histories remain
open, as do R5/R6-R8 obligation creation and discharge, arbitrary-support
Pull/Expand materializer identities, complete Package E and N1-N10, and global
routing. This result is not unconditional SaturatePositive, BCELReady or
ZeroSlack, exact PCCMin, or a total encoded-size polynomial runtime theorem.
No semantic minimum is executed by these constructors. Deterministic CNFSAT in P
and the eligible root remain open.

No fixed checkpoint or global gate closes.

## Reviewed interfaces and verification

The sixteen general interfaces below have exact compiled type fingerprints.
Their dependencies are contained in `propext` and `Quot.sound`; none requires
a project-specific axiom or `Classical.choice`.

- `PNP.DirectWire.WireCarrier.exposed_unpack`
- `PNP.DirectWire.WireCarrier.unpack_exposed`
- `PNP.DirectWire.WireCarrier.normalize_output`
- `PNP.DirectWire.WireCarrier.normalize_field`
- `PNP.DirectWire.WireCarrier.normalize_exact_accounting`
- `PNP.DirectWire.WireCarrier.normalize_quiescent`
- `PNP.DirectWire.WireCarrier.normalize_idempotent`
- `PNP.DirectWire.WireCarrier.field_producer_visible`
- `PNP.DirectWire.WireCarrier.splice_output`
- `PNP.DirectWire.WireCarrier.splice_field`
- `PNP.DirectWire.WireCarrier.splice_exact_accounting`
- `PNP.DirectWire.WireCarrier.splice_strict_gain`
- `PNP.DirectWire.WireCarrier.splice_checked`
- `PNP.DirectWire.WireCarrier.splice_failure_iff`
- `PNP.DirectWire.WireCarrier.production_boundary_isInput`
- `PNP.DirectWire.WireCarrier.production_compiles`

The regression has a kernel-checked example with equal ordinary outputs but
unequal hidden field values. It also checks hidden-only producers, repeated and
reordered observations, input and constant fields, empty dimensions, actual
normalization savings, safe and cyclic interleaved splices, and smaller and
larger production replacements. Runtime execution is test evidence, not theorem
authority; the arbitrary-dimension theorems remain kernel checked.

Sources: [carrier construction](../lean/PNP/NANDWireCarrier.lean),
[axiom audit](../lean-audit/PNPWireCarrierAxiomAudit.lean),
[regressions](../lean-regression/PNPWireCarrier.lean),
[hostile publication contracts](../audits/lean-wire-carrier0.test.mjs), and
[the milestone plan](./plans/2026-09-12-computed-wire-backed-carrier-transport.md).

## Progress and publication cadence

Formal artefact coverage: 226 of 228 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Formal artefact coverage is evidence-ledger coverage, not proof completion.
The fixed-weight estimate is not confidence, a probability of success, or a
time estimate. See [the canonical progress model](../status/PROOF_PROGRESS.json).

Publication decision: defer PNPLabs. This computational-value transport component
does not complete the full carrier or change the coherent published M231 bottom
line. Core evidence and submilestone notifications continue independently of
website publication.
