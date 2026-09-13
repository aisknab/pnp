# Computed full-mode wire cancellation

M254 computes one source-derived R6 cancellation case and pairs it with actual
R8 restoration for unresolved computational fields. It is not the complete
manuscript obligation calculus.

Formal artefact coverage: 230 of 232 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Specification and local agreement

The route follows section 6.1 of the manuscript pinned by
[the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json). R5 creates
a lost-bit obligation; R6 requires a full-mode witness, not merely projected
equality. Section 6.2 requires traceable obligation handling, and section 4
requires actual physical materializer charges.

Local quotient agreement is a premise: the supplied replacement agrees with all
ordinary outputs and all kept computational fields for every input valuation.
This reuses the precise M252 interface. It does not assume forgotten-field
equality or a supplied successful full expansion. Neither the local replacement
nor its agreement is derived by this construction.

## Retained representatives from the original source

Computational source identity, not arbitrary semantic equality, determines the
implemented R6 case. Scan the original ordinary observations and kept fields
in canonical order. A representative must have exactly the same original
Source data as the forgotten field. The result records its retained observation
index and original source equality.

A forgotten field cannot represent another forgotten field merely because both
have the same source. Masked false padding is not evidence for a forgotten field.
A gate number in a different program is not original source identity. The actual
replacement observation at the selected index supplies the value; the local
agreement and original source equality derive its full correctness.

This scan may leave syntactically different but semantically equal wires
unresolved. It does not claim complete semantic cancellation and uses no
exhaustive semantic minimizer.

## One actual remaining materializer

A field is resolved if it is kept or has a computed retained representative.
Construct one materializer for all unresolved original wires. If every field
resolves, use an explicit zero-gate carrier. Repeated unresolved fields share
physical ownership; they are not charged once per field.

Rebind resolved forgotten fields on the actual replacement program to their
retained observations, then join that carrier with the remaining materializer.
The theorem preserves every ordinary output and every ordered computational
field for every valuation.

| Object or decision | Exact boundary |
| --- | --- |
| Materializer charge | The actual constructed missing-wire program's gate count |
| Fully resolved fields | Zero materializer gates |
| Expanded gate count | Replacement gates plus materializer charge |
| Accepted original saving | The complete expanded count is strictly below the original count |
| Comparison with an earlier normalized materializer | No universal improvement theorem is claimed |

Whole-word gain is not proper-support Package E. A physical gate-count bound is
not a complete encoded-size polynomial execution theorem.

## Full discharges and unique identities

For each actually forgotten coordinate, compute an R5 creation followed by
either an R6 cancellation with its canonical source match or an R8 restoration
with its unresolved condition. Both branches bind their full-value witness to
the actual expanded source and the original R5 source for every valuation.

Generated creations and discharges cover exactly the forgotten coordinates.
Their replay closes with no pending obligations. The replay validates creation
identities across the whole transcript, including already discharged entries.
It rejects identity reuse, discharge-before-creation and wrong-coordinate
discharges. This is a checked adjacent-pair lifecycle, not an implementation of
arbitrary obligation dependency DAGs or every R7 rule.

## Reviewed general interfaces

All twenty-six interfaces build from the explicit PNP root with exact reviewed
kernel-type fingerprints. The representative-existence theorem depends only on
propext; the other twenty-five have dependencies propext and Quot.sound. There
are no project-specific axioms or Classical.choice dependencies in these interfaces.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.WireMatchedCancellation.representative_isSome_iff` | Computed matching succeeds exactly when an original retained observation has the same literal source. |
| `PNP.DirectWire.WireMatchedCancellation.observation_value` | Precise local quotient agreement preserves each genuinely retained full observation. |
| `PNP.DirectWire.WireMatchedCancellation.Representative.full_value` | Original source identity derives the forgotten field value from its retained representative. |
| `PNP.DirectWire.WireMatchedCancellation.allResolved_sound` | The computed all-resolved test covers every field. |
| `PNP.DirectWire.WireMatchedCancellation.charge_allResolved` | A completely resolved field set needs no materializer gates. |
| `PNP.DirectWire.WireMatchedCancellation.missing_unresolved_field` | Every unresolved field retains its original full value in the actual materializer. |
| `PNP.DirectWire.WireMatchedCancellation.charge_bound` | The actual materializer gate count is bounded by the original gate count. |
| `PNP.DirectWire.WireMatchedCancellation.visible_resolved_field` | The visible replacement restores each resolved field. |
| `PNP.DirectWire.WireMatchedCancellation.expanded_charge` | Expansion charges replacement gates plus the single actual materializer. |
| `PNP.DirectWire.WireMatchedCancellation.expanded_output` | Every ordinary output is preserved under local quotient agreement. |
| `PNP.DirectWire.WireMatchedCancellation.expanded_field` | Every ordered computational field is preserved under the same local agreement. |
| `PNP.DirectWire.WireMatchedCancellation.expanded_equivalent` | The expanded ordinary-output word is equivalent to the original. |
| `PNP.DirectWire.WireMatchedCancellation.Discharge.full_value` | Either typed discharge branch carries the original full value. |
| `PNP.DirectWire.WireMatchedCancellation.discharge_source_exact` | A computed discharge names the actual expanded source at its coordinate. |
| `PNP.DirectWire.WireMatchedCancellation.discharge_isR6_iff` | The computed discharge is R6 exactly when the source scan finds a retained match. |
| `PNP.DirectWire.WireMatchedCancellation.discharge_full_value` | The computed discharge has the original field value for every valuation. |
| `PNP.DirectWire.WireMatchedCancellation.checkedGain_isSome_iff` | Whole-word gain is accepted exactly when the fully paid expansion is smaller. |
| `PNP.DirectWire.WireMatchedCancellation.CheckedGain.checked` | An accepted result carries strict ordinary equivalence, all field values and exact cost. |
| `PNP.DirectWire.WireMatchedCancellation.created_exact` | Generated creations are exactly the forgotten coordinates. |
| `PNP.DirectWire.WireMatchedCancellation.discharged_exact` | Generated discharges are exactly the forgotten coordinates. |
| `PNP.DirectWire.WireMatchedCancellation.creation_iff` | A coordinate is created exactly when its field is forgotten. |
| `PNP.DirectWire.WireMatchedCancellation.discharge_iff` | A coordinate is discharged exactly when its field is forgotten. |
| `PNP.DirectWire.WireMatchedCancellation.created_nodup` | Generated creation identities are unique. |
| `PNP.DirectWire.WireMatchedCancellation.discharged_nodup` | Generated discharge identities are unique. |
| `PNP.DirectWire.WireMatchedCancellation.replay_closed` | The mixed generated transcript closes with no pending obligations. |
| `PNP.DirectWire.WireMatchedCancellation.replay_rejects_duplicate_ids` | A transcript with reused creation identities is rejected. |

See the [Lean source](../lean/PNP/NANDWireMatchedCancellation.lean),
[root-importing regressions](../lean-regression/PNPWireMatchedCancellation.lean),
[exact axiom audit](../lean-audit/PNPWireMatchedCancellationAxiomAudit.lean),
[publication contracts](../audits/lean-wire-matched-cancellation0.test.mjs) and
[recorded plan](./plans/2026-09-13-computed-full-mode-wire-cancellation.md).

## Regression and hostile evidence

Kernel-checked negative examples reject incorrect ordinary or kept replacement
data, and distinguish a locally legal replacement from its wrong forgotten
value. Bounded executions exercise retained ordinary and kept aliases, mixed
R6 and R8 branches, repeated and reordered sources, two unrepresented forgotten
fields, masked padding, unrelated gate indices, all-kept and all-forgotten
masks, free input and constant fields, no ordinary outputs, empty dimensions,
paid gain and no-net-gain rejection.

Runtime execution is test evidence, not theorem authority. The exported
theorems quantify over arbitrary finite dimensions and all valuations. Contract
mutations reject supplied scans, hidden representatives, omitted or duplicated
cost, unbound or weakened full witnesses, reused identities, finite-only types,
extra axioms, stale fingerprints and widened claims.

## Remaining boundary and publication decision

This is an original-source-identity computational R6 case, not every semantic cancellation or the complete manuscript obligation calculus. The keep mask, replacement and precise local quotient agreement are inputs; forgotten-field equality, supplied representatives, materializer weights and global correctness certificates are not. Syntactically different but semantically equal wires may remain unresolved. No universal comparison with independently normalized earlier materializers is proved. A whole-word strict gain is not a proper-support Package E certificate. The full manuscript carrier, noncomputational profile fields, R7 and arbitrary dependency DAGs, all-trace N1-N10 normalization, complete Package E, global routing, unconditional SaturatePositive, BCELReady and ZeroSlack, exact PCCMin and total encoded-size polynomial construction, runtime, output and certificate bounds remain open. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

No fixed checkpoint or global gate closes. Publication decision: defer PNPLabs.
The coherent M231 public source pin remains unchanged. The complete carrier,
all-trace normalization, obligation dependency calculus, Package E and global
polynomial proof obligations remain open.
