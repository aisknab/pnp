# Computed constant and unary replacement on arbitrary completed supports

M257 reconstructs the manuscript's constant/unary R7 replacement for arbitrary
finite computational supports, including a sole incoming external gate.
The replacement and its successful compilation are derived from the actual source.

Formal artefact coverage: 233 of 235 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Specification and scope

The route follows section 6.1 of the manuscript pinned by
[the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json).
R7 needs an actual full-value realization. Package E additionally requires a
proper support and strict physical saving; sections 4 and 6.2 govern ownership
and matched Pull/Expand accounting.

The original gate count, ambient input count, ordinary output width, field count
and selected finite support are arbitrary. Repeated terminal records are allowed.
The selected support is an input to the local rule, not a certificate that the
rule succeeds. The actual boundary and complete frontier are computed from the
full exposed carrier, including every computational field.

The option-valued query succeeds exactly when the computed boundary has zero or
one port. Boundaries with more than one incoming port are rejected. No replacement,
truth table, agreement, rank, acyclicity certificate, compilation order or compiler
result is supplied.

## Why the external-gate case is safe

A replacement with the right open function is not by itself an acyclic splice.
An early selected gate can feed an exterior gate that is itself the sole incoming
boundary to a later selected gate. A replacement that unnecessarily depends on
that boundary at the early port could introduce a feedback cycle.

General open-evaluation prefix causality shows that a selected observation before
the external boundary gate has equal values under both open boundary valuations.
The actual minimum zero/unary constructor represents such observations by literal
constants. It does not merely supply an equivalent word.

Derive the rank from original indices: exterior gate g has rank 2*g, and the
possible replacement NOT has rank 2*b+1 for boundary gate b. Earlier consumers
receive constants; later consumers and the shared NOT have decreasing
dependencies. Empty and primary-input boundaries use their constructive
primary-boundary argument.

Every recognized arbitrary support compiles. The proof covers every open boundary
valuation, even a Boolean value that cannot arise from the complete original
circuit. Whole-circuit induced values alone would not justify this local rule.

The two shared modules receive append-only causality and rank lemmas. All earlier
definitions, theorem statements and proof bodies are retained unchanged.

## Minimum complete word and actual expansion

The local word represents the full extracted frontier. Its minimum is among every
equivalent complete local open realization, not ordinary-output-only agreement.
All required negations share at most one physical NOT. A hidden selected field
can therefore prevent a spurious zero-gate replacement.

Compile against the original exterior, retained exactly once. Every ordinary
output and every computational field is preserved at every ambient valuation.
The result has exact replacement-plus-exterior charge and cannot increase the
original gate count. Strict ambient saving is equivalent to strict local saving
for this fixed physical partition.

Proper gain additionally requires positive actual exterior. Whole-support saving
is not a proper-support Package E certificate. The query succeeds whenever a
strictly smaller equivalent complete local word exists on a recognized proper
support. This is not a minimum over different exteriors or all ambient circuits.

## Full-value R7 witnesses

For each original source-bound R5 identity, construct the R7 witness from the
actual expanded source at the same field coordinate. The source equality and
its complete original field value are proved at every ambient valuation.

Masked padding, unrelated sources and caller-supplied full-value certificates
cannot replace this witness. The theorem does not assemble all manuscript
obligation dependency DAGs or every R5-R8 interaction.

## Reviewed general interfaces

All 31 interfaces build from the explicit PNP root with exact reviewed kernel-type
fingerprints. One is axiom-free, one uses only Quot.sound and 29 use only
propext and Quot.sound. No project-specific axiom or Classical.choice is used.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.terminalOpenGateEvaluation_prefix_congr` | Open evaluation is unchanged when the earlier boundary inputs agree. |
| `PNP.DirectWire.terminalOpenGateEvaluation_single_gate_prefix` | Observations before the sole external boundary gate are constant in its open input. |
| `PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary` | The single-boundary splice rank is valid for literal earlier constants and at most one gate. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.constantWord_source` | Each zero-input output is represented by a literal constant. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.unaryWord_source_of_constant` | An open-constant unary observation uses a literal constant source. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.localWord_source_of_constant` | The zero/unary dimension transport retains literal constants. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.replacement_agreement` | The source-derived replacement preserves the complete open frontier. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.replacement_gate_bound` | The replacement uses at most one physical gate. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.replacement_minimal` | No equivalent complete local open realization uses fewer gates. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.replacement_nonincrease` | The replacement cannot exceed the selected gate count. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.replacement_early_constant` | Frontier gates earlier than the external boundary become literal constants. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.graph_wellFounded` | The actual source-derived rebound graph is well founded. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.compile_isSome` | Every recognized zero/unary support compiles without a supplied success certificate. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.original_charge` | Original physical charge is selected support plus exterior. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.expanded_output` | Every ordinary ambient output is preserved. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.expanded_field` | Every full computational field is preserved. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.expanded_equivalent` | The ordinary ambient implementation is equivalent. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.expanded_charge` | Expansion counts the actual replacement and original exterior exactly once. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.expanded_nonincrease` | Expansion cannot increase the original gate count. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.expanded_gain_iff` | Strict global saving is equivalent to strict local saving for this partition. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.proper_iff_exterior_positive` | Proper selected support is equivalent to positive actual exterior. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.attempt_isSome_iff` | The public query recognizes exactly zero- or one-port boundaries. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.attempt_output` | Every accepted result preserves ordinary outputs. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field` | Every accepted result preserves full fields. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.attempt_nonincrease` | Every accepted result is nonincreasing. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.attempt_charge` | Every accepted result has exact derived accounting. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_source_exact` | The witness names the actual expanded source for the original R5 identity. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_full_value` | The witness retains the original full field value at every valuation. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_isSome_iff` | The proper query separates boundary recognition, exterior positivity and strict saving. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_complete` | Any smaller complete local realization implies proper-query success. |
| `PNP.DirectWire.WireUnaryArbitrarySupport.ProperGain.checked` | An accepted proper gain carries strict equivalence, full fields and exact charge. |

See the [main Lean source](../lean/PNP/NANDWireUnaryArbitrarySupport.lean),
[prefix-causality extension](../lean/PNP/ResidualTerminalSupportExtraction.lean),
[single-boundary rank extension](../lean/PNP/NANDArbitrarySupportSplice.lean),
[root-importing regressions](../lean-regression/PNPWireUnaryArbitrarySupport.lean),
[exact axiom audit](../lean-audit/PNPWireUnaryArbitrarySupportAxiomAudit.lean),
[publication contracts](../audits/lean-wire-unary-arbitrary-support0.test.mjs)
and [recorded plan](./plans/2026-09-13-computed-unary-arbitrary-support.md).

## Regression and hostile evidence

Sixteen guarded scenarios cover the potential external-gate feedback cycle,
a globally unrealizable boundary bit, repeated non-prefix support, constants,
no saving, whole support, multiboundary rejection, empty support, a nonzero
primary-input index, hidden selected negation, one shared NOT, selected and
exterior field-only words, free fields and empty dimensions.

Runtime execution is test evidence, not theorem authority. The general compiler
success, minimum, preservation, accounting and full-value R7 statements are
kernel checked for arbitrary finite dimensions.

Hostile source and publication contracts reject supplied ranks or compiler
results, omitted frontier observations, fictitious constants, duplicate exterior
charge, weakened signatures, extra assumptions, stale fingerprints, false
proper gains and widened global claims.

## Remaining boundary and publication decision

Arbitrary support refers to the choice of finite physical support in a computational wire carrier, not arbitrary boundary width or the full manuscript carrier. Boundaries with more than one incoming port are rejected. The minimum is over complete local open realizations for the fixed extracted frontier, not over all ambient circuits or different exteriors. A whole-support saving is not a proper-support Package E certificate. Prefix causality and the source-derived rank prove termination of this compiler, not uniformly polynomial encoded-size execution. Noncomputational profile fields, arbitrary obligation dependency DAGs, every R5-R8 interaction, all-trace N1-N10 normalization, complete Package E, global routing, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and total encoded-size polynomial construction, runtime, output and certificate bounds remain open. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

No fixed checkpoint or global gate closes. Publication decision: defer PNPLabs.
The coherent M231 public source pin remains unchanged while the computational
carrier components await a major publication-worthy end-to-end capability.
