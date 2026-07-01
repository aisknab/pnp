# PkgC direct-binding gap-transition seed

Current coordinate:

```text
PNP-DIRECT-BIND-PKGC-SEPARATING-CONSUMERS-GAP-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/PKGC_DIRECT_BINDING_GAP_SEED.json
```

Checker:

```bash
node pcc-direct-bind-pkgc-separating-consumers0.mjs --json
```

This seed binds the historical Section 22 `PkgC` theorem-ledger row to current request traces, full-restoration universes, nonsingleton separating-consumer routing, quotient-to-full key preservation, singletonization, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

The current PkgC closure row is a gap-transition surface:

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
pkgcDirectBindingGapSeedReady = true
directCheckerBindingComplete = false
fullHistoricalPkgCTheoremDischarged = false
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

The next PkgC work must replace the represented gap-transition surface with a full separating-consumer proof artifact only after unrestricted final soundness and finite-to-unbounded uniformity are represented by accepted checkers rather than seed/gap ledgers.
