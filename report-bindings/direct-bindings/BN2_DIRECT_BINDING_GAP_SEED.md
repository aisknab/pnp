# BN2 direct-binding gap-transition seed

Current coordinate:

```text
PNP-DIRECT-BIND-BN2-SIDE-TIGHT-GAP-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/BN2_DIRECT_BINDING_GAP_SEED.json
```

Checker:

```bash
node pcc-direct-bind-bn2-side-tight0.mjs --json
```

This seed binds the historical Section 22 `BN2` theorem-ledger row to the current side-tight coherent optima, saturated support square, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

The current BN2 closure row is a gap-transition surface:

```text
currentCoverageClass = uniformity-gap-surface
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

## Current scope

```text
bn2DirectBindingGapSeedReady = true
directCheckerBindingComplete = false
fullHistoricalBN2TheoremDischarged = false
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

The next BN2 work must replace the represented gap-transition surface with a full side-tight coherent-optima proof artifact only after unrestricted final soundness and finite-to-unbounded uniformity are represented by accepted checkers rather than seed/gap ledgers.
