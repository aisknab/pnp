# BN3 direct-binding gap-transition seed

Current coordinate:

```text
PNP-DIRECT-BIND-BN3-REQUEST-ENVELOPE-GAP-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/BN3_DIRECT_BINDING_GAP_SEED.json
```

Checker:

```bash
node pcc-direct-bind-bn3-request-envelope0.mjs --json
```

This seed binds the historical Section 22 `BN3` theorem-ledger row to the current stable request systems, simultaneous finite envelopes, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

The current BN3 closure row is a gap-transition surface:

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
bn3DirectBindingGapSeedReady = true
directCheckerBindingComplete = false
fullHistoricalBN3TheoremDischarged = false
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

The next BN3 work must replace the represented gap-transition surface with a full request-envelope proof artifact only after unrestricted final soundness and finite-to-unbounded uniformity are represented by accepted checkers rather than seed/gap ledgers.
