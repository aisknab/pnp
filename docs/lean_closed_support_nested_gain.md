# Computed nested-support cost and positivity transport

Current coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-280`.

Formal artefact coverage: 256 of 258 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Exact scope

For arbitrary finite wire carriers, keep masks and two raw seed lists whose computed completed supports are physically nested, derive the exact gate difference and crossing bindings. Extend the actual full or quotient reference minimum inside the common ambient input domain, preserving the larger padded ordinary interface and exact required computational-field availability, including false values. The derived comparisons prove that either minimum grows by at most the added physical gates, that full slack and support size minus quotient minimum are monotone, and that positive full slack or projection defect remains positive in the completed larger support. Raw-seed inclusion derives the physical inclusion. No cost inequality, field-equality certificate or optimizer is supplied to the final theorem.

## Limits

This compares already completed dependency-closed supports in the computational-wire-profile model. It does not prove preservation of an arbitrary raw witness's initial positivity during completion, transparency of every intermediate event, monotonicity of projection defect alone, complete manuscript profile semantics, discovery of a proper positive support, global routing or unconditional SaturatePositive, BCELReady or ZeroSlack. Reference minimization, matching and influence computations remain exhaustive; complete polynomial PCCMin runtime, output-size and certificate bounds are not proved. The eligible root theorem remains absent and P = NP is not proved.

## Construction and proof interfaces

The [selection layer](../lean/PNP/NANDClosedSupportNestedSelection.lean)
computes the exact physical difference between two completed supports and
derives the real smaller-support interface needed by every crossing gate.
The [program](../lean/PNP/NANDClosedSupportNestedProgram.lean) keeps the
common ambient inputs unchanged and appends only that difference.
The [candidate](../lean/PNP/NANDClosedSupportNestedCandidate.lean) restores
the larger support’s padded ordinary output word.

The [source-origin proof](../lean/PNP/NANDClosedSupportNestedOrigin.lean)
accounts for every value as either a smaller-comparison source or an actual
added gate. The [profile proof](../lean/PNP/NANDClosedSupportNestedProfile.lean)
establishes both directions of field availability, not just preservation of
true observations. Fixing unused ambient inputs could create an observation
that should remain false; the construction therefore does not specialize them.

The [cost bounds](../lean/PNP/NANDClosedSupportNestedCost.lean) instantiate
these comparisons with the computed full and quotient reference minima.
Exact physical partitioning then yields the slack and positivity results.
The [seed interface](../lean/PNP/NANDClosedSupportNestedGain.lean) derives
physical inclusion from raw-seed inclusion. A seed argument is not a claim
that its unsaturated support already satisfies the completed-support theorem.

The principal checked statements are:

```lean
theorem full_minimum_cost_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).fullMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).fullMinimum + (snapshot target keep large).supportSize

theorem quotient_minimum_cost_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).quotientMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).quotientMinimum + (snapshot target keep large).supportSize

theorem full_slack_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).fullSlack ≤ (snapshot target keep large).fullSlack

theorem positive_mono (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (positive : 0 < (snapshot target keep small).fullSlack ∨
      0 < (snapshot target keep small).projectionDefect) :
    0 < (snapshot target keep large).fullSlack ∨
      0 < (snapshot target keep large).projectionDefect

theorem seed_positive (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large)
    (positive : 0 < (snapshot target keep small).fullSlack ∨
      0 < (snapshot target keep small).projectionDefect) :
    0 < (snapshot target keep large).fullSlack ∨
      0 < (snapshot target keep large).projectionDefect
```

## Independent regression boundaries

The [regression](../lean-regression/PNPClosedSupportNestedGain.lean) checks
eight general type contracts, six kernel guards and eleven executable cases.
They cover empty and equal supports, proper nesting, crossing wires, hidden
and exterior fields, both keep-mask extremes, duplicate records, rejected
reverse inclusion and the field-observation error caused by fixing an unused
ambient input. Finite examples test the general construction; they are not
theorem authority or additional roadmap milestones.

The [axiom audit](../lean-audit/PNPClosedSupportNestedGainAxiomAudit.lean)
imports the explicit root and checks all 36 reviewed theorem closures.
Only the standard axioms `propext` and `Quot.sound` occur; no project-specific
assumption or unexpected classical-choice dependency is introduced.

The [source contract](../audits/lean-closed-support-nested-gain0.test.mjs)
and [compiled publication contract](../audits/lean-closed-support-nested-gain-publication0.test.mjs)
reject weakened types, supplied cost or profile authority, lost inclusion,
altered fingerprints, missing evidence and widened global or polynomial claims.

## Progress and publication

M280 derives actual full and quotient comparison circuits for every pair of computed nested completed supports, replacing a supplied cost-balance premise with a physical construction and exact field observations. It closes the completed-support enlargement edge of positive-slack preservation, but not raw-witness completion, manuscript-wide profile semantics, global route completeness or polynomial minimization. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Publication decision: defer. The result proves general preservation between computed completed supports, not the unresolved initial-completion boundary or a global saturation theorem. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

See the [integration plan](./plans/2026-09-20-computed-nested-support-positivity.md),
[canonical progress ledger](../status/PROOF_PROGRESS.json),
[preceding whole-support minimum bridge](./lean_closed_whole_minimum.md) and
[pinned manuscript archive](../archive/legacy-v0/ARCHIVE.json).
