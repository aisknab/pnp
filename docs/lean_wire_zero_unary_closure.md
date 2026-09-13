# Computed full-field zero/unary descent and normalization closure

M259 combines source-derived proper and whole-span zero/unary gain searches
with physical normalization, restarting after each actual gain until they
reach a common scoped fixed point.

Formal artefact coverage: 235 of 237 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Manuscript dependency and scope

The construction follows the full-span policy's "Whole-span cheaper word gives
descent" lemma and the NormalizeOrGain/PCCMin restart edge in the manuscript
pinned by [the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json).
Section 6.1 governs proper-support R7; a whole-span saving is instead a strict
residual descent, not a local VerifyDW gain.

All finite input, gate, ordinary-output and computational-field dimensions
remain arbitrary. Every ordinary output and every computational field is
preserved at every valuation. The search class is supports with zero or one
actual incoming boundary wire, not necessarily zero or one declared input.

The previously compiled proper-support search supplies one branch. M259
derives the other branch and the complete gain/re-normalization execution;
it does not accept a support family, optimizer, trajectory, stopping witness
or completeness certificate from its caller.

## Whole-span and proper gains are distinct

The whole support is computed from all original physical gate indices. Its
exterior is zero and its extracted gate count is the original gate count.
The existing complete zero/unary word constructor and successful compiler
produce the actual replacement when its local gate count is strictly smaller.

Proper gains retain a positive original exterior. Whole-span gains have zero
exterior. A tagged result preserves this distinction and proves full-field
agreement, strict saving and exact original-gate accounting for either branch.

Whole-span descent is not a proper-support Package E certificate.
No proof turns zero exterior into a positive-exterior local witness.

## Complete combined search in the zero/unary class

The combined procedure tries the source-derived proper-support search first,
then the derived whole-span branch. For any physical support with at most one
actual incoming wire and any strictly smaller equivalent complete local word,
the combined search succeeds.

A positive exterior uses the proper-support completeness theorem. Zero exterior
forces every original gate to be selected. Physical extraction congruence
then transfers that support's complete open function and strict saving to the
canonical whole support. This covers repeated records and other records that
select the same gates without introducing caller-supplied coverage data.

The mathematical comparison word and semantic agreement are premises of the
general completeness theorem, not executable search inputs. A negative result
excludes every gain in this exact zero/unary support class, including whole-span
gains. It does not prove that every circuit optimization has been exhausted.

## Actual restart closure and common stopping

Each iteration computes physical normalization with all computational fields
exposed, then runs the combined search on the normalized carrier. A successful
result constructs its actual expanded carrier and restarts normalization.
The recursion terminates by a strict decrease of the actual physical gate
count; normalization is nonincreasing and every accepted gain is strict.

The computed execution includes a trace of the actual normalization and gain
results. Its general checked theorem proves ordinary-output agreement,
preservation of every full computational field, physical quiescence, absence
of both gain branches on the same final carrier, exact telescoping gate savings
and an iteration bound by the gates retired.

The closure is idempotent at its returned carrier. Search-call accounting
includes the final negative query. These are operational statements about the
computed closure, not the existence of a supplied valid execution.

Reference minima occur only in specifications and proofs, not execution.
Semantic invariance preserves the reference minimum and turns exact gate
savings into exact residual-slack retirement. The normalization/gain iteration
count is bounded by initial residual slack, and search calls by that slack
plus one.

An iteration or search-call bound is not a total polynomial runtime theorem.
Extraction, candidate discovery, compilation and complete encoded-size costs
still require their own bounds.

## A scoped fixed point need not be globally minimal

The guarded negative regression uses the two-input circuit
NAND(NAND(x,x), NAND(x,y)). Its ordinary output is x, so an explicit zero-gate
input projection is a strictly smaller equivalent carrier. Nevertheless,
the physical passes and every zero/unary gain route are quiet.

The regression kernel-checks this strict gain and positive global residual
slack. This is not a counterexample to the scoped closure theorem; it prevents
the stronger and unsupported inference that this restricted fixed point is
a global minimum or unconditional ZeroSlack.

## Reviewed general interfaces

All 27 interfaces build from the explicit PNP root and have exact reviewed
kernel-type fingerprints. Their axiom closures contain only propext and
Quot.sound, with no Classical.choice or project-specific axiom.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.WireZeroUnaryClosure.whole_selected` | The computed whole records select every original physical gate. |
| `PNP.DirectWire.WireZeroUnaryClosure.whole_exterior` | The whole support has exactly zero original exterior charge. |
| `PNP.DirectWire.WireZeroUnaryClosure.whole_gateCount` | Whole extraction retains exactly the original gate count. |
| `PNP.DirectWire.WireZeroUnaryClosure.whole_not_proper` | A whole support cannot be a proper-support R7 witness. |
| `PNP.DirectWire.WireZeroUnaryClosure.all_gates_of_zero_exterior` | Zero original exterior forces every physical gate to be selected. |
| `PNP.DirectWire.WireZeroUnaryClosure.WholeGain.checked` | The whole branch constructs a strict full-field-preserving actual descent. |
| `PNP.DirectWire.WireZeroUnaryClosure.wholeGain_isSome_iff` | Executable whole-branch recognition matches its checked zero/unary strict saving. |
| `PNP.DirectWire.WireZeroUnaryClosure.wholeGain_complete` | Any eligible zero-exterior local saving makes the derived whole branch succeed. |
| `PNP.DirectWire.WireZeroUnaryClosure.Gain.full_field` | Both tagged gain branches preserve every computational field. |
| `PNP.DirectWire.WireZeroUnaryClosure.Gain.branch_boundary` | Proper and whole branches retain positive and zero exterior respectively. |
| `PNP.DirectWire.WireZeroUnaryClosure.Gain.exact_accounting` | Actual gain expansion accounts for the original gate count exactly. |
| `PNP.DirectWire.WireZeroUnaryClosure.nextGain_isSome_iff` | The combined search succeeds exactly when one of its actual branches succeeds. |
| `PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_iff` | No combined result means both actual branches are absent. |
| `PNP.DirectWire.WireZeroUnaryClosure.nextGain_complete` | Every zero/unary support with a cheaper equivalent complete word yields a result. |
| `PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_excludes` | No result excludes every strict saving in the scoped support class. |
| `PNP.DirectWire.WireZeroUnaryClosure.normalization_accounting` | Physical normalization has exact original-gate accounting. |
| `PNP.DirectWire.WireZeroUnaryClosure.normalization_iterations` | Physical normalization iterations are bounded by its actual gate savings. |
| `PNP.DirectWire.WireZeroUnaryClosure.Trace.checked` | An actual trace preserves full semantics, reaches common stopping and accounts for savings. |
| `PNP.DirectWire.WireZeroUnaryClosure.Trace.searchCalls_le` | Search calls, including the terminal negative call, satisfy the trace bound. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_checked` | The carrier-only executable closure proves the full common-stopping and accounting interface. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_of_stopped` | A physically and search-quiescent carrier is returned unchanged. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_idempotent` | Running the closure on its returned carrier leaves that carrier unchanged. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_no_smaller_zeroUnary` | The computed final carrier admits no cheaper complete zero/unary support word. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_referenceMinimum` | The final carrier has the same semantic reference minimum as the initial carrier. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_residualSlack` | Actual gate savings retire global residual slack exactly. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_gainIterations_le_residualSlack` | Normalization/gain iterations are bounded by initial residual slack. |
| `PNP.DirectWire.WireZeroUnaryClosure.run_searchCalls_le_residualSlack` | Combined search calls are bounded by initial residual slack plus one. |

See the [main Lean source](../lean/PNP/NANDWireZeroUnaryClosure.lean),
[root-importing regressions](../lean-regression/PNPWireZeroUnaryClosure.lean),
[exact axiom audit](../lean-audit/PNPWireZeroUnaryClosureAxiomAudit.lean),
[publication contracts](../audits/lean-wire-zero-unary-closure0.test.mjs)
and [recorded plan](./plans/2026-09-13-computed-zero-unary-descent-closure.md).
No inherited mathematical definition, statement or proof body is changed.

## Regression and hostile evidence

Sixteen guarded runtime cases cover empty dimensions, free ordered fields,
minimal words, whole-span-only savings, proper savings with exterior fields,
hidden selected fields, sharing before a gain, successive proper and whole-span
gains, gain-triggered constant propagation, no ordinary outputs, constant-only
and dead-support normalization, a nonminimum common fixed point and unused
declared inputs.

Tiny support enumeration is a regression oracle, not the production algorithm.
The unused-input fixture uses bounded selected valuations, not all valuations.
Five general or kernel examples complement the runtime cases.
Runtime execution is test evidence, not theorem authority.

Source and compiled contracts reject weakened theorem types, supplied
completeness or stopping certificates, omitted full fields, assumption-backed
substitutes, changed fingerprints and claims of global or polynomial completion.
The source-signature parser treats a let binding in a theorem type as part of
the type, so the entire checked closure interface remains protected.

## Remaining boundary and publication decision

The stopping result is restricted to physical normalization and zero/one-actual-boundary computational gains. It is not global minimality: a guarded physically quiescent common fixed point has an explicit smaller equivalent carrier and strictly positive global residual slack. Whole-span descent is not relabelled as a proper-support Package E certificate. Preserving every computational field does not reconstruct the full manuscript carrier, noncomputational profile fields or arbitrary obligation dependency DAGs. Wider boundaries, every R5-R8 interaction, all-trace N1-N10 normalization, complete Package E, global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-size polynomial runtime, output and certificate bounds remain open. A gate-decrease or search-call bound is not a total polynomial execution theorem; inherited extraction, compilation and candidate-search costs still require their own bounds. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

Publication decision: defer a separate PNPLabs cycle for M259.
The selected M253-M258 release and its major website batch remain independently
gated. Reuse the exact core proof and report evidence at the website boundary;
do not rebuild Lean for PNPLabs.
