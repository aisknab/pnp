# Computed constant and unary frontier replacement

M256 reconstructs a source-derived constant/unary frontier component of
manuscript R7. It joins the computed complete frontier with an actual minimum
local word before expansion into the original circuit.

Formal artefact coverage: 232 of 234 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Specification and arbitrary ambient dimensions

The route follows section 6.1 of the manuscript pinned by
[the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json): R7 realizes
a unary cut with full-value discharge, and Package E requires a proper support,
an actual equivalent open word and a strict physical saving. Sections 4 and 6.2
require actual ownership and matched Pull/Expand accounting.

Original gate count, ambient input count, ordinary output width and computational
field count are arbitrary. The input is the actual carrier and its keep mask.
No local replacement, truth table, semantic agreement, support map, compilation
order, compiler result or minimizer is supplied.

## Complete source-derived frontier

Compute the predecessor cone of ordinary outputs and kept field sources, then
complete its frontier against every actual observation and consumer in the
original full computational word. Forgotten selected fields remain frontier
observations; forgotten exterior fields retain their original physical producers.

Recognize the actual incoming boundary length. Zero or one incoming port is
accepted. A larger boundary is outside this rule even if its function might
admit some other simplification. Every recognized frontier compiles.

For zero boundary inputs, evaluate the actual extracted source at the unique
valuation and construct its zero-gate constant word. For one input, use the
complete M255 unary constructor through checked dimension transport. All local
observations are included, and every required negation shares one actual gate.

This is local full-frontier minimality, not ordinary-output-only agreement.
A hidden selected negation therefore prevents a false zero-gate replacement.

## Actual expansion and matched charge

The computed predecessor cone has a primary-input-only incoming boundary.
Its existing compiler-success theorem supplies an actual result for the derived
replacement; the caller supplies neither an order nor a successful compiler run.

Expand against the original exterior, retained exactly once. Every ordinary
output and every computational field is preserved for every ambient valuation,
including exterior fields depending on inputs unrelated to the unary boundary.

The result's gate count is exactly the computed replacement count plus the
original exterior count. Minimum local size implies nonincrease. Strict ambient
saving is equivalent to strict local saving under this same physical partition.

Proper-support gain also requires positive actual exterior. Whole-support saving
is not a proper-support Package E certificate. A minimal local word, empty
support or nonstrict saving cannot fabricate a proper gain.

The minimum theorem compares every implementation of the complete fixed local
open function. It is not a global minimum over ambient circuits or different
choices of exterior.

## Full-value source-bound R7 discharge

For an original source-bound R5 identity, construct its R7 witness from the actual
expanded source at that field coordinate. Its full value agrees with the original
lost source in the original program at every ambient valuation.

The agreement is derived from the complete local realization and actual expansion.
Masked padding, a source from an unrelated program or a supplied full-value
certificate cannot replace this witness. The result does not assemble all
manuscript obligation dependency DAGs or every R5-R8 interaction.

## Reviewed general interfaces

All thirty interfaces build from the explicit PNP root with exact reviewed
kernel-type fingerprints. Two are axiom-free, one uses only Quot.sound and
twenty-seven use only propext and Quot.sound. No project-specific axiom or
Classical.choice is used.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.WireUnaryFrontier.constantWord_value` | The actual zero-input source determines each constant observation. |
| `PNP.DirectWire.WireUnaryFrontier.constantWord_gateCount` | The constant realization uses no physical gates. |
| `PNP.DirectWire.WireUnaryFrontier.unaryWord_value` | The unary realization preserves every local observation. |
| `PNP.DirectWire.WireUnaryFrontier.unaryWord_minimal` | The unary result is minimal among every equivalent complete word. |
| `PNP.DirectWire.WireUnaryFrontier.unaryWord_gate_bound` | The unary result uses at most one shared gate. |
| `PNP.DirectWire.WireUnaryFrontier.localWord_value` | The checked zero/unary dimension transport preserves all local values. |
| `PNP.DirectWire.WireUnaryFrontier.localWord_minimal` | The complete local word is minimal among all equivalent implementations. |
| `PNP.DirectWire.WireUnaryFrontier.localWord_nonincrease` | The complete local gate count cannot increase. |
| `PNP.DirectWire.WireUnaryFrontier.localWord_gate_bound` | A recognized local word uses at most one gate. |
| `PNP.DirectWire.WireUnaryFrontier.replacement_agreement` | The constructed frontier agrees at every open valuation and port. |
| `PNP.DirectWire.WireUnaryFrontier.replacement_minimal` | Every equivalent complete local realization has at least this many gates. |
| `PNP.DirectWire.WireUnaryFrontier.replacement_nonincrease` | The replacement cannot exceed the pulled support's gate count. |
| `PNP.DirectWire.WireUnaryFrontier.replacement_gate_bound` | The replacement has at most one gate. |
| `PNP.DirectWire.WireUnaryFrontier.replacement_zero_gateCount` | A zero-boundary replacement uses no gates. |
| `PNP.DirectWire.WireUnaryFrontier.expanded_output` | Every ordinary ambient output is preserved. |
| `PNP.DirectWire.WireUnaryFrontier.expanded_field` | Every actual computational field is preserved. |
| `PNP.DirectWire.WireUnaryFrontier.expanded_equivalent` | The ordinary ambient implementation remains equivalent. |
| `PNP.DirectWire.WireUnaryFrontier.expanded_charge` | The actual charge is replacement plus the original exterior exactly once. |
| `PNP.DirectWire.WireUnaryFrontier.expanded_nonincrease` | Expansion cannot increase the original physical gate count. |
| `PNP.DirectWire.WireUnaryFrontier.expanded_gain_iff` | Strict ambient saving is exactly strict local saving. |
| `PNP.DirectWire.WireUnaryFrontier.attempt_isSome_iff` | The query succeeds exactly when the actual boundary has at most one port. |
| `PNP.DirectWire.WireUnaryFrontier.attempt_output` | Every accepted result preserves ordinary outputs. |
| `PNP.DirectWire.WireUnaryFrontier.attempt_field` | Every accepted result preserves all computational fields without a replacement premise. |
| `PNP.DirectWire.WireUnaryFrontier.attempt_nonincrease` | Every accepted result is nonincreasing. |
| `PNP.DirectWire.WireUnaryFrontier.attempt_charge` | Every accepted result has the exact derived physical accounting. |
| `PNP.DirectWire.WireUnaryFrontier.dischargeR7_source_exact` | R7 names the actual expanded source for the original R5 identity. |
| `PNP.DirectWire.WireUnaryFrontier.dischargeR7_full_value` | The R7 source has the original full field value at every ambient valuation. |
| `PNP.DirectWire.WireUnaryFrontier.checkedProperGain_isSome_iff` | The proper query checks recognition, positive exterior and strict saving. |
| `PNP.DirectWire.WireUnaryFrontier.checkedProperGain_complete` | Any smaller equivalent complete local word implies proper-query success. |
| `PNP.DirectWire.WireUnaryFrontier.ProperGain.checked` | An accepted proper gain carries strict equivalence, all fields and exact charge. |

See the [Lean source](../lean/PNP/NANDWireUnaryFrontier.lean),
[root-importing regressions](../lean-regression/PNPWireUnaryFrontier.lean),
[exact axiom audit](../lean-audit/PNPWireUnaryFrontierAxiomAudit.lean),
[publication contracts](../audits/lean-wire-unary-frontier0.test.mjs) and
[recorded plan](./plans/2026-09-13-computed-unary-frontier-replacement.md).

## Regression and hostile evidence

Thirteen small guarded scenarios cover a unary boundary at a nonzero original
input index, forgotten exterior fields depending on other inputs, hidden selected
negations, repeated and reordered observations sharing one actual gate, constant
frontiers, multiboundary rejection, whole-support savings, already minimal
supports, free fields, field-only interfaces and empty dimensions.

Runtime execution is test evidence, not theorem authority. General all-valuation,
success, minimum, accounting and full-value discharge theorems are kernel checked.
Hostile tests reject incomplete words, wrong input dimensions, supplied
replacements or compiler results, quotient-only fields, duplicated exterior
charge, ordinary-only minima, unbound R7 witnesses, false proper gains,
assumptions, stale fingerprints and widened publication claims.

## Remaining boundary and publication decision

This is source-derived constant/unary R7 realization for the computed visible predecessor cone, not every arbitrary ambient support or an external-gate boundary. Minimum size is relative to the complete fixed local frontier, not all ambient circuits with different exteriors. A whole-support saving is not a proper-support Package E certificate. More-than-unary boundaries are rejected rather than supplied with correctness certificates. Finite source evaluation and actual compiler termination are not encoded-size polynomial runtime theorems. The full manuscript carrier, noncomputational profile fields, arbitrary obligation dependency DAGs, every R5-R8 interaction, all-trace N1-N10 normalization, complete Package E, global routing, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and total encoded-size polynomial construction, runtime, output and certificate bounds remain open. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

Finite source evaluation and compiler termination do not establish polynomial
encoded runtime. The implementation proves actual gate counts, not the complete
execution, output-encoding or certificate-size bounds for general PCCMin.

No fixed checkpoint or global gate closes. Publication decision: defer PNPLabs.
The coherent M231 public source pin remains unchanged while these computational
components await a major publication-worthy end-to-end capability.
