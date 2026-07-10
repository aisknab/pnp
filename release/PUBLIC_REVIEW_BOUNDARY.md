# Historical public-review non-activation boundary

> **Superseded checker boundary:** This June 2026 surface records historical assertion-checker
> behavior. It is not current theorem-status authority. Formal reconstruction is in progress, and
> the repository does not currently establish `P = NP`. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01
```

Machine-readable manifest:

```text
release/PUBLIC_REVIEW_BOUNDARY.json
```

Checker:

```bash
node pcc-public-review-boundary0.mjs --json
```

This boundary historically aggregated the then-current status file, release ladder, gap ledger,
sanitized report surfaces, theorem-anchor surface, public-surface baseline, Section 22 direct-binding
index, and Section 22 runner into one non-activation audit.

It is an aggregate boundary, not a theorem-activation surface.

## Historical scope

```text
publicReviewBoundaryReady = true
publicTheoremEmissionAllowedByBoundary = false
finalTheoremReadyByBoundary = false
publicSurfaceBaselineFrozen = true
historicalReportSanitized = true
historicalTheoremAnchorsNonEmitting = true
releaseLadderBlocked = true
gapLedgerBlocksPublicEmission = true
section22ExecutableSurfaceIndexed = true
section22RunnerBound = true
```

## Boundary

The historical release boundary recorded:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Blocked release nodes

```text
UnrestrictedFinalSoundnessRepresented -> Release.UnrestrictedFinalSoundness
InternalTheoremActivationCandidate -> Release.UnrestrictedFinalSoundness
PublicTheoremEmissionCandidate -> ExternalReview.Acceptance
```

The historical sealed report artifacts may still contain direct theorem-emission wording. Current
authority comes only from the formal-reconstruction status, which keeps those artifacts subordinate.
