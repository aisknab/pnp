# Computed unary full-word realization

M255 reconstructs the unary computational realization component of manuscript
R7 directly from the original carrier. It does not accept a supplied
replacement, truth table, local agreement or minimizer.

Formal artefact coverage: 231 of 233 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Specification and arbitrary dimensions

The route follows section 6.1 of the manuscript pinned by
[the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json): R7 realizes
a unary cut and must discharge the full obligation, not merely its projection.
Sections 2 and 4 require ordered interfaces and actual physical ownership;
section 6.2 supplies the later normalization-transport obligations.

One boundary input is the unary rule, not a fixed gate-count or schedule-slot
restriction. The original program size, ordinary output width and computational
field count are arbitrary. This milestone handles the complete computational
word of that unary carrier. Embedding it into every ambient cut remains open.

## Source-derived construction

Expose ordinary outputs followed by every computational field. Evaluate those
actual observations at the false and true unary inputs. The four possible value
pairs identify a constant false, the input, its negation or a constant true.

The constructor uses an actual empty program when no observation needs negation.
Otherwise it uses the existing single NOT NAND program. All negated observations
share that one actual gate, including repeated and reordered fields and ordinary
outputs. Unpacking the complete word recovers their separate ordered interfaces.

No Boolean field is supplied by a proof-only record. The implementation and its
full agreement are both derived from the original computational source.

## Exact full-word minimum

The all-valuation theorem preserves every ordinary output and every field.
The exact result has zero gates if none of those complete observations requires
negation, and one gate otherwise.

A zero-gate source can only be the boundary input or a constant. It cannot be
true at input false and false at input true. This gives a lower bound against
every equivalent complete carrier, not an enumeration of candidate programs.

Full-word minimality is not ordinary-output-only minimality. A constant ordinary
output with a negated computational field still requires one gate. A replacement
matching only that ordinary output is not a full realization.

The strict-gain query compares the actual computed result with the original
physical gate count. If any equivalent complete unary carrier is smaller, the
minimum theorem proves that this query succeeds. Whole-word gain is not
proper-support Package E.

## Source-exact full R7 discharge

For a source-bound R5 creation, construct its R7 discharge from the actual new
source at the same computational field coordinate. Its full witness compares
that source in the computed program with the original lost source in the
original program, for every unary valuation.

The keep mask and forgotten coordinate identify the old R5 obligation; they do
not supply its replacement value or correctness. Neither masked padding nor a
same-numbered gate in an unrelated program is a valid witness.

This typed R7 component does not yet implement arbitrary obligation dependency
DAGs or merge all R5-R8 rules into the complete manuscript calculus.

## Reviewed general interfaces

All eighteen interfaces build from the explicit PNP root with exact reviewed
kernel-type fingerprints. Five are axiom-free and thirteen depend only on
propext and Quot.sound. No project-specific axiom or Classical.choice is used.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.WireUnaryRealization.observation_value` | The two actual unary source values determine every valuation. |
| `PNP.DirectWire.WireUnaryRealization.needsNegation_iff` | The full observation scan detects exactly a required negation. |
| `PNP.DirectWire.WireUnaryRealization.implementation_value` | The constructed complete word agrees with every source observation. |
| `PNP.DirectWire.WireUnaryRealization.realize_output` | Every ordered ordinary output is preserved. |
| `PNP.DirectWire.WireUnaryRealization.realize_field` | Every computational field is preserved without an agreement premise. |
| `PNP.DirectWire.WireUnaryRealization.realize_equivalent` | The ordinary output word remains equivalent. |
| `PNP.DirectWire.WireUnaryRealization.realize_full_equivalent` | Every exposed computational observation remains equivalent. |
| `PNP.DirectWire.WireUnaryRealization.realize_gateCount` | The actual cost is zero or one shared gate. |
| `PNP.DirectWire.WireUnaryRealization.negation_requires_gate` | No zero-gate unary implementation can produce negation. |
| `PNP.DirectWire.WireUnaryRealization.realize_minimal` | The result is minimal among every equivalent complete carrier. |
| `PNP.DirectWire.WireUnaryRealization.realize_nonincrease` | The computed gate count cannot exceed the input count. |
| `PNP.DirectWire.WireUnaryRealization.realize_gate_bound` | The actual realization uses at most one gate. |
| `PNP.DirectWire.WireUnaryRealization.R7Discharge.full_value` | A source-exact R7 record carries the original full field value. |
| `PNP.DirectWire.WireUnaryRealization.dischargeR7_source_exact` | The computed R7 discharge names its actual new source. |
| `PNP.DirectWire.WireUnaryRealization.dischargeR7_full_value` | The computed R7 source has the original value at every valuation. |
| `PNP.DirectWire.WireUnaryRealization.checkedGain_isSome_iff` | The query accepts exactly a strictly smaller computed whole word. |
| `PNP.DirectWire.WireUnaryRealization.checkedGain_complete` | Any smaller full equivalent carrier makes the computed query succeed. |
| `PNP.DirectWire.WireUnaryRealization.CheckedGain.checked` | An accepted gain preserves strict ordinary equivalence, every field and exact cost. |

See the [Lean source](../lean/PNP/NANDWireUnaryRealization.lean),
[root-importing regressions](../lean-regression/PNPWireUnaryRealization.lean),
[exact axiom audit](../lean-audit/PNPWireUnaryRealizationAxiomAudit.lean),
[publication contracts](../audits/lean-wire-unary-realization0.test.mjs) and
[recorded plan](./plans/2026-09-13-computed-unary-full-word-realization.md).

## Regression and hostile evidence

Kernel-checked negative examples separate ordinary agreement from full field
agreement and distinguish unrelated actual programs. Small guarded executions
cover constants, identity, shared negation, repeated and reordered observations,
a two-gate tautology, empty interfaces, no ordinary outputs, no fields,
all-kept and all-forgotten R5 masks, strict gain and no-gain rejection.

Runtime execution is test evidence, not theorem authority. The general
all-valuation and minimum theorems are kernel checked. Hostile contracts reject
supplied tables and agreements, omitted fields, free negation, duplicate
physical charges, ordinary-only minima, unbound or weakened R7 witnesses,
finite-only signatures, assumptions, stale fingerprints and widened claims.

## Remaining boundary and publication decision

This is a complete unary computational word realization component for manuscript R7, not an arbitrary ambient-cut embedding, every R7 case or the complete manuscript obligation calculus. Minimum size is relative to all exposed computational observations, not ordinary outputs alone. A whole-word strict gain is not a proper-support Package E certificate. The keep mask and source-bound R5 identity are used only by the discharge interface; no supplied full-value agreement is a construction premise. There is no enumeration of implementations, but evaluating two unary inputs with recursive Program.eval does not prove polynomial encoded runtime. The full manuscript carrier, noncomputational profile fields, arbitrary obligation dependency DAGs, all-trace N1-N10 normalization, complete Package E, global routing, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and total encoded-size polynomial construction, runtime, output and certificate bounds remain open. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

The two unary valuations do not establish polynomial encoded runtime.
Recursive Program.eval may repeat source evaluation; this milestone proves
actual output gate size, not a complete execution or encoded certificate bound.

No fixed checkpoint or global gate closes. Publication decision: defer PNPLabs.
The coherent M231 public source pin remains unchanged while these computational
components await a major publication-worthy end-to-end capability.
