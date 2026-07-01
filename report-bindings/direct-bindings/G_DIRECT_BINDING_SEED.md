# G direct-binding locked-NAND threshold seed

Current coordinate:

```text
PNP-DIRECT-BIND-G-LOCKED-NAND-THRESHOLD-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/G_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-locked-nand-threshold0.mjs --json
```

This seed binds the historical Section 22 `G` theorem-ledger row to the current locked NAND SAT threshold small-model evidence, macro truth-table surface, baseline/threshold row, residual-slack-at-most-four surface, complexity implication ledger, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

The current G closure row is a locked-NAND seed surface:

```text
currentCoverageClass = locked-nand-seed-surface
closureStatus = direct-binding-seed-upgrade-needed
blockingGaps = [
  "GAP-003-BoundedSmallModelsNotUniformProof",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

## Current scope

```text
gDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalGTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
directBindingBlockedByGaps = true
```

## Boundary

The seed is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The next G work must replace the bounded locked-NAND SAT small-model surface with a full uniform threshold proof artifact covering every SAT input size under polynomial-time generation. Until then, this row remains a seed, not a completed direct checker binding.
