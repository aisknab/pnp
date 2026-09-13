# Source-bounded ordered physical boundary extraction

M260 computes the existing incoming physical boundary from actual gate sources,
without scanning unused declared primary-input positions. The new executable
path is proved exactly equal to the old ordered reference list.

Formal artefact coverage: 236 of 238 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Manuscript dependency and scope

Sections 2 and 3 of the manuscript pinned by the
[immutable archive manifest](../archive/legacy-v0/ARCHIVE.json) define incoming
physical ports by actual gate-source crossings. The PCCMin construction needs
these ports to be computed from its carrier. M258's proper-support discovery and
M259's zero/unary restart closure used a correct extractor that still enumerated
every declared input position, even when nearly all inputs were unused.

This milestone refines that implementation dependency. It does not change the
manuscript route or the physical crossing predicate. All input, gate, output and
profile dimensions remain arbitrary, as does the list of terminal records.

## Source-driven construction

The executable extractor collects the two sources of every actual physical gate.
A constant contributes no wire; an input or gate source contributes that exact
ambient coordinate. This occurrence list has length at most twice the gate count.

The existing crossing predicate filters those occurrences. A generic list helper
then removes duplicates and sorts by an injective coordinate: primary inputs
first, followed by gate outputs in index order. Neither helper enumerates the
ambient input type. No boundary list, order witness or completeness certificate
is supplied by a caller.

Every physical crossing is proved to occur in this source list. The canonical
output is proved equal to the old reference as a list, not merely as a set or by
length. Consequently the order, exact coordinates and multiplicity agree.

The active `terminalBoundaryPorts` now delegates to the source-driven extractor.
Reference equality preserves existing physical extraction and support interfaces.
The generic canonicalizer also proves equality with any ordered, duplicate-free
reference having exactly the same members under an injective coordinate map.

The ambient enumeration remains a theorem-side reference, not the active extractor.

## Proven bounds and their limits

Both the occurrence list and emitted boundary have length at most `2 * gates`,
independent of the number of unused declared input positions. The emitted list
has no duplicates and is in canonical primary-input-before-gate-output order.

These are structural size bounds, not total polynomial execution theorems.
Comparison, deduplication, crossing checks, record processing and encoded index
costs still need explicit execution accounting for a complete complexity claim.
This result does not discharge the full encoded-size polynomial PCCMin checkpoint.

## Reviewed general interfaces

All 23 reviewed interfaces build from the explicit PNP root and have pinned
kernel-type fingerprints. Seven depend only on `propext`, fifteen on `propext`
and `Quot.sound`, and one uses no axioms. No reviewed interface depends on
`Classical.choice`, a project-specific axiom or an unchecked implementation.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.SourceListOrder.mem_unique` | Removing duplicates preserves exactly the original list members. |
| `PNP.DirectWire.SourceListOrder.unique_nodup` | The computed unique list contains no duplicate entries. |
| `PNP.DirectWire.SourceListOrder.unique_length_le` | Removing duplicates cannot increase list length. |
| `PNP.DirectWire.SourceListOrder.mem_canonical` | Canonicalization preserves exactly the original list members. |
| `PNP.DirectWire.SourceListOrder.canonical_nodup` | The canonical list is duplicate-free. |
| `PNP.DirectWire.SourceListOrder.canonical_length_le` | Canonicalization cannot increase list length. |
| `PNP.DirectWire.SourceListOrder.canonical_ordered` | The canonical list is ordered by its coordinate key. |
| `PNP.DirectWire.SourceListOrder.ordered_eq_of_mem` | Two strictly ordered lists with the same members and injective keys are equal. |
| `PNP.DirectWire.SourceListOrder.canonical_eq_reference` | The computed canonical list equals the exact ordered duplicate-free reference. |
| `PNP.DirectWire.TerminalSupportWire.orderCode_injective` | The primary-input-before-gate-output coordinate is injective. |
| `PNP.DirectWire.allTerminalSupportWires_strictOrder` | The existing ambient reference has strict canonical coordinate order. |
| `PNP.DirectWire.Source.mem_terminalWireOccurrences_iff` | Occurrence membership agrees with use of that exact nonconstant source wire. |
| `PNP.DirectWire.Source.terminalWireOccurrences_length` | An individual gate source contributes at most one wire occurrence. |
| `PNP.DirectWire.terminalSourceWireOccurrences_length` | All actual gate sources contribute at most twice the gate count. |
| `PNP.DirectWire.terminalBoundaryWire_mem_sourceOccurrences` | Every physical crossing occurs among the actual gate-source wires. |
| `PNP.DirectWire.terminalBoundaryPortsSourceDriven_eq_reference` | The source-driven boundary equals the exact ordered ambient reference list. |
| `PNP.DirectWire.terminalBoundaryPortsSourceDriven_length` | The source-driven boundary has length at most twice the gate count. |
| `PNP.DirectWire.terminalBoundaryPortsSourceDriven_nodup` | The source-driven boundary contains no duplicate ports. |
| `PNP.DirectWire.terminalBoundaryPortsSourceDriven_ordered` | The source-driven boundary has canonical coordinate order. |
| `PNP.DirectWire.terminalBoundaryPorts_reference` | The active extractor preserves the exact old reference list. |
| `PNP.DirectWire.terminalBoundaryPorts_length` | The active extractor emits at most twice the gate count in ports. |
| `PNP.DirectWire.terminalBoundaryPorts_nodup` | The active extractor emits no duplicate ports. |
| `PNP.DirectWire.terminalBoundaryPorts_ordered` | The active extractor emits ports in canonical coordinate order. |

See the [physical implementation](../lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean),
[generic canonicalizer](../lean/PNP/NANDSourceListOrder.lean),
[root-importing regressions](../lean-regression/PNPSourceBoundedPhysicalBoundary.lean),
[exact axiom audit](../lean-audit/PNPSourceBoundedPhysicalBoundaryAxiomAudit.lean),
[publication contracts](../audits/lean-source-bounded-physical-boundary0.test.mjs)
and [recorded plan](./plans/2026-09-13-source-bounded-physical-boundary.md).

## Inherited standard-axiom review

The source-driven canonical sorting proof adds Lean's standard `Quot.sound`
dependency to 28 previously propext-only reviewed interfaces. Every inherited
reviewed theorem type, defining module and publication fingerprint is unchanged.
No project axiom or `Classical.choice` enters those closures. Their current
inventory, status and exact audit expectations record the change; historical
release objects retain their original transcripts.

The 28 affected names and unchanged fingerprints are pinned in this milestone's
compiled regression. This dependency was already within the foundational audit
allowlist; no fixed weighted checkpoint or global gate changes.

## Regression and hostile evidence

Fifteen guarded runtime cases cover empty dimensions, constants, duplicate
sources, primary and gate ports, reversed source order, nonconsecutive support,
repeated or unordered records, internal selected producers and whole support.
Small cases compare the exact old reference with the new executable output.

Four cases use a billion declared inputs with at most two actual gates. They
check sparse primary and mixed ports without evaluating the ambient reference,
enumerating all input slots or enumerating valuations. The existing sixteen
zero/unary closure runtime cases also pass through the new active extractor.

Runtime execution is test evidence, not theorem authority.
The general list equality, crossing completeness, ordering and length bounds
are separate kernel-checked theorems.

Hostile source contracts reject omitted gate sources, repeated ports, reversed
ordering, wrong coordinates, ambient-input scanning, supplied completeness,
weakened theorem types and unchecked implementation overrides. Compiled contracts
pin every reviewed type and axiom closure and reject inflated publication claims.

## Remaining boundary and publication decision

Occurrence and output bounds are structural size bounds, not total encoded-input-size polynomial execution theorems. The reference equality preserves the existing physical semantics; it does not establish a new global minimization result. The old ambient enumeration remains only as a theorem-side specification, never the active boundary implementation. No caller-supplied boundary or completeness certificate is introduced. The full manuscript carrier, arbitrary obligation dependency DAGs, every normalization and gain interaction, complete Package E and global route coverage remain open. These results do not prove unconditional SaturatePositive, BCELReady or ZeroSlack, exact general PCCMin, or total polynomial runtime, output and certificate bounds for the complete construction. Runtime execution is regression evidence, not theorem authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

Publication decision: defer a separate PNPLabs cycle for M260.
The eligible M258 major batch remains independently gated. PNPLabs reuses the
exact verified core theorem and report evidence; it does not rebuild Lean.
