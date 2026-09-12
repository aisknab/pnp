# M246: computed dead-support full-mode acceptance

M246 checks the actual M245 computed proper dead-support replacement against every coordinate of an input finite profile observation system and every observed obligation role. It accepts a full-carrier result only when the complete profile agrees and observed obligations are closed, or returns a precise rejecting outcome. Eight general interfaces cover exact acceptance, first failures, physical semantics, properness and exact size/slack descent. The observation system remains input data: the manuscript carrier, semantic dependency graph, R5/R6-R8 ledger, complete Package E and global PCCMin route are not derived.

## Legacy dependency and construction

The pinned manuscript's section 5 Package E boundary requires a proper support,
a same-carrier replacement and a closed final obligation ledger. M245 derives the
physical frame and proper dead-support gain from the actual implementation.
M246 closes the next checked-acceptance edge for that result, not the entire
manuscript admissibility theorem.

For arbitrary finite input/output dimensions and a finite observation system,
`classifyDeadSupportFullMode` first runs the actual `deadSupportProperGain`.
If this returns no result, the classifier reports `noProperSupport`. Otherwise it
uses the complete profile mismatch scan on the computed replacement. A mismatch
returns the first coordinate, its role and the preceding agreeing coordinates.
Only after all profile coordinates agree does it scan obligation-role coordinates.
A true obligation bit returns the first open obligation and preceding closed
obligation prefix. With both scans clear, it constructs `DeadSupportFullModeGain`
and the existing `TerminalFullCarrierRealization`.

No result, profile-invariance premise or correctness certificate is supplied by the caller.
The finite observation system itself remains input data. The scan inspects its
complete carrier, not a quotient projection; true non-obligation coordinates are
not mistaken for open obligations. Accepted replacements preserve the complete
ordered Boolean output word for every input by M245's general semantics theorem.

## Reviewed general interfaces

- `PNP.DirectWire.firstTerminalOpenObligation_eq_none_iff`: The obligation scan returns none exactly when all observed obligation-role coordinates are discharged.
- `PNP.DirectWire.firstTerminalOpenObligation_spec`: A returned coordinate is an actual open obligation and every earlier obligation is closed.
- `PNP.DirectWire.DeadSupportFullModeGain.currentObligationsDischarged`: An accepted full-mode gain also discharges observed obligations on the current implementation by complete profile equality.
- `PNP.DirectWire.classifyDeadSupportFullMode_accepted_iff`: Acceptance is equivalent to computed properness, equality at every finite profile coordinate and discharge of replacement obligations.
- `PNP.DirectWire.classifyDeadSupportFullMode_noProperSupport_iff`: The no-proper-support outcome is equivalent to failure of this specific computed physical-gain constructor.
- `PNP.DirectWire.DeadSupportFullModeGain.fullProfileMinimum`: Accepted full-carrier equivalence preserves the full-profile reference minimum as a specification result.
- `PNP.DirectWire.DeadSupportFullModeGain.checked`: An accepted result has nonempty proper support, complete semantics, profile equality, discharged current/replacement observations, exact size/slack accounting and strict residual descent.
- `PNP.DirectWire.classifyDeadSupportFullMode_checked`: Every computed branch carries its exact rejection evidence or the accepted result's closed obligations and strict physical gain.

All eight are built through the explicit `PNP` root with exact reviewed kernel
types and dependencies limited to `propext` and `Quot.sound`. The compiled
inventory and publication ledger carry the authoritative fingerprints.

## Limits and remaining obligations

Checking observed obligation bits is not a constructed R5 creation or R6-R8 discharge ledger.
It does not derive the manuscript carrier, its semantic dependency graph or the
connection between those observed bits and every required rule application.
Consequently it does not by itself establish complete Package E admissibility.
A matching profile with an open obligation is rejected; neither a mismatch nor
an open obligation is silently converted into a completed global route.

No-proper-support rejection excludes only this computed dead-support route.
It does not rule out a different physical gain, whole-circuit gain or a smaller
semantic implementation. Zero-width observation systems make no additional
manuscript completeness claim. All-dead or no-dead cases retain the strict
proper-support boundary.

The classifier does not enumerate all supports, implementations, valuations or
reference minima. The full-profile reference minimum appears only in a
specification theorem, not in execution. The input observation function has no
encoded-size polynomial bound here; finite scans alone are not a proof of total
polynomial runtime.

Full manuscript carrier derivation, semantic dependency completeness, R5/R6-R8
ledger construction, complete N1-N10 normalization, the total PCCMin oracle,
unconditional SaturatePositive, BCELReady and ZeroSlack, deterministic CNFSAT in P
and the eligible root theorem remain open. No fixed checkpoint or global gate closes.

## Regression and publication evidence

Arbitrary-dimension type regressions cover all eight statements. Bounded runtime
fixtures exercise real acceptance, first profile mismatch, an open obligation
despite equal profiles, true non-obligation coordinates, a zero-width profile,
no-dead/all-dead/empty cases and a mismatch concealed by quotient projection.
Runtime execution is test evidence, not theorem authority.

Source and compiled hostile contracts reject skipped coordinates, wrong roles,
fake accepted failure branches, weakened or supplied theorem types, altered
fingerprints, extra axioms and widened manuscript/global claims. The durable
workflow executes the exact audited interfaces and regressions. Current source,
status, generated mirrors, progress and report are checked together.

## Current metrics and publication decision

Formal artefact coverage: 222 of 224 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Formal artefact coverage is only coverage of the scoped evidence ledger, whose
denominator can grow; it is not proof completion. The fixed-weight estimate is
not confidence that P=NP is true, a probability of success or a time estimate.

Publication decision: defer PNPLabs. This internal acceptance boundary does not
change the coherent published M231 bottom line. Verified submilestone messages
remain independent of website publication cadence.

See the [recorded plan](plans/2026-09-12-computed-dead-support-full-mode.md),
[computed dead-support context](lean_pccmin_dead_support_context.md),
[canonical progress policy](proof_progress.md) and
[conditional concrete final-report bridge](lean_concrete_final_report_bridge.md).
