# M280: computed nested-support cost and positivity transport

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-280`.

The general proof, constructive axiom review and focused explicit-root checks
are complete. This plan records the remaining publication and release gates.
Release must use the actual verified M279 main-branch merge, not its feature tip.

Formal artefact coverage: 256 of 258 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and exact dependency

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json),
at `final-pnp-proof-report-docs-hardened-7072f8d-sealed`, names
`transparentSaturationCostBalanced` in RW-SaturatePositive. It is construction
specification and provenance, not Lean theorem authority.

The selected missing edge is a cost-bounded full or quotient realization
inside every larger completed dependency-closed support, not only the whole
circuit. The construction derives the physical difference, interfaces and
observations from one arbitrary finite carrier and two raw seed lists.
A supplied balance inequality or profile-equality certificate cannot replace
this derivation. The existing terminal-minimum bridge is not counted again.

## Unbounded abstraction and exact theorem types

In `PNP.DirectWire.ClosedSupportNestedGain`, `snapshot` recomputes costs
after `ClosedSupportObservation.records` completes a raw seed. `Included`
compares the computed physical gate selections. Raw-seed inclusion derives
that relation. These types do not assert positivity of an unsaturated support.

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

The result preserves full slack and support size minus quotient minimum.
It preserves positive full slack or projection defect as a disjunction;
monotonicity of projection defect alone is not asserted.

## Construction and verification order

1. Derive the exact physical difference and count partition, then the
   smaller-support interface required by every crossing wire.
2. Keep all ambient inputs, append only the difference and derive the
   larger padded ordinary output word.
3. Prove both directions of exact computational-field availability.
   Instantiate the comparisons with the actual full and quotient minima.
4. Derive cost inequalities and combined positivity constructively.
   Compile isolated modules and inspect their exact axiom closures.
5. Check eight general contracts, six kernel guards and eleven executable
   cases, including false observations and rejected non-inclusion.
6. Reconcile root imports, both inventory producers and frozen source
   contracts before the root build and root-importing checks.
7. Export inventory once, seal its actual fingerprints, and update status,
   progress, test expectations and current documentation before validation.
8. Run targeted publication checks, exact durable workflow blocks and the
   deduplicated full validation union. Retain independent exact-object
   reproduction and normal PR/post-merge checks; do not repeat core Lean
   compilation in the website publication boundary.

## Remaining obligations and progress decision

This compares already completed dependency-closed supports in the computational-wire-profile model. It does not prove preservation of an arbitrary raw witness's initial positivity during completion, transparency of every intermediate event, monotonicity of projection defect alone, complete manuscript profile semantics, discovery of a proper positive support, global routing or unconditional SaturatePositive, BCELReady or ZeroSlack. Reference minimization, matching and influence computations remain exhaustive; complete polynomial PCCMin runtime, output-size and certificate bounds are not proved. The eligible root theorem remains absent and P = NP is not proved.

M280 derives actual full and quotient comparison circuits for every pair of computed nested completed supports, replacing a supplied cost-balance premise with a physical construction and exact field observations. It closes the completed-support enlargement edge of positive-slack preservation, but not raw-witness completion, manuscript-wide profile semantics, global route completeness or polynomial minimization. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

## Publication decision

Publication decision: defer. The result proves general preservation between computed completed supports, not the unresolved initial-completion boundary or a global saturation theorem. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.
