# M248: computed physical normalization closure

M248 computes a terminating priority loop over constant propagation, NAND sharing and output-cone pruning. Its constructed trace preserves every ordered output and records exact physical savings. All three passes are quiet on the same final result, and re-execution returns that result unchanged. These twelve general interfaces establish operational quiescence, not semantic minimality, complete manuscript normalization or the global PCCMin route.

## Legacy dependency and actual construction

The pinned manuscript's section 5 Traceable normalization requires complete
semantics and non-increasing physical size. M242, M244 and M247 supply actual
physical sharing, output-cone pruning and literal constant-propagation passes.
M248 closes their common operational stopping edge in the normalization stage.

The fixed priority is constant propagation, then NAND sharing, then output-cone
pruning. The loop runs the first pass with positive computed savings, records
that actual gain and restarts the check on its result. It stops only when all
three savings are zero on the same final implementation. Every nonterminal edge
strictly decreases physical gate count, which is the termination measure.
No normalizer, oracle, result or stopping certificate is supplied by the caller.

The trace records selected pass identities, rejected earlier priorities, strict
physical gains and the final common stopping evidence. Its saved-gate sum
telescopes exactly: final gate count plus saved gates equals initial gate count.
There are no more gain iterations than saved gates, and no more than initial
residual slack. The complete ordered output word is unchanged for every input.
The final result is operationally idempotent under this same loop.

## Reviewed general interfaces

- `PNP.DirectWire.physicalNormalizationPass_equivalent`: Every actual pass preserves complete ordered-output semantics.
- `PNP.DirectWire.physicalNormalizationPass_exact_accounting`: Actual savings account for the exact retained-gate difference.
- `PNP.DirectWire.PhysicalNormalizationGain.checked`: Each selected gain is strict and respects fixed pass priority.
- `PNP.DirectWire.nextPhysicalNormalizationStep_checked`: The computed selector either constructs a gain or checks all three passes.
- `PNP.DirectWire.PhysicalNormalizationTrace.checked`: The finite trace has complete semantics, common quiescence and exact cost.
- `PNP.DirectWire.runPhysicalNormalization_checked`: The actual loop derives its result and trace from the implementation alone.
- `PNP.DirectWire.runPhysicalNormalization_of_quiescent`: A quiescent implementation is returned unchanged.
- `PNP.DirectWire.runPhysicalNormalization_idempotent`: Running the complete closure twice has the same result as once.
- `PNP.DirectWire.runPhysicalNormalization_referenceMinimum`: Equivalent results have the same semantic reference minimum.
- `PNP.DirectWire.runPhysicalNormalization_residualSlack`: Residual slack drops by exactly the total actual saved gates.
- `PNP.DirectWire.runPhysicalNormalization_gainIterations_le_residualSlack`: Gain iterations are bounded by initial slack, not by an asserted runtime.
- `PNP.DirectWire.physicalClosureNormalizer_checked`: The public normalizer surfaces positive total saving as a strict gain.

All twelve are built through the explicit PNP root, with exact reviewed
kernel-type fingerprints and only the standard propext and Quot.sound axioms.
The compiled inventory and publication ledger carry the authoritative records.

## Stopping and manuscript boundary

The result establishes operational quiescence for exactly three physical passes.
Quiescence does not imply semantic minimality or ZeroSlack. The two-gate
NAND(x, NAND(x,x)) fixture is quiet for every pass and remains unchanged, while
a zero-gate constant-true word is checked as strictly smaller and equivalent.

This is not every R1 structural identity or complete N1-N10 normalization.
The whole-program trace does not supply the arbitrary-support Pull/Expand
materializer identities required by the full Traceable normalization theorem.
Full-profile preservation, the derived manuscript carrier, the R5/R6-R8
obligation lifecycle ledger and complete Package E remain open.

Semantic reference minima occur only in specification theorems and are never
executed by the loop. An iteration bound is not a runtime bound for constructing
or checking a pass. No uniformly encoded-size polynomial construction, runtime,
output-size or certificate-size theorem is established here. The total PCCMin
oracle, unconditional SaturatePositive, BCELReady and ZeroSlack, deterministic
CNFSAT in P and the eligible root remain open.
No fixed checkpoint or global gate closes.

## Regression and publication evidence

Arbitrary-dimension type regressions cover all twelve interfaces. Bounded
fixtures exercise each actual route, priority with multiple available routes,
interacting constant/sharing/pruning gains, repeated/input/constant outputs,
empty dimensions, stable re-execution and the nonminimum quiescent example.
Runtime execution is test evidence, not theorem authority.

Hostile contracts reject dropped passes, wrong priority, incomplete stopping,
fabricated trace savings or iterations, non-decreasing recursion, supplied
construction authority, weakened types, changed fingerprints, extra axioms
and widened manuscript or global claims. The durable workflow runs the exact
reviewed axiom audit and bounded regressions.

## Current metrics and publication decision

Formal artefact coverage: 224 of 226 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Formal artefact coverage measures only the current evidence ledger; its
denominator can grow and it is not proof completion. The fixed-weight estimate
is not confidence that P=NP is true, a probability of success or a time estimate.

Publication decision: defer PNPLabs. This physical sub-loop does not change the
coherent published M231 bottom line. Meaningful verified submilestone
notifications remain independent of website publication cadence.

See the [recorded plan](plans/2026-09-12-computed-physical-normalization-closure.md),
[computed constant propagation](lean_pccmin_constant_propagation.md),
[computed sharing](lean_pccmin_constructive_nand_sharing.md),
[output-cone pruning](lean_pccmin_output_cone_pruning.md) and
[canonical progress policy](proof_progress.md).
