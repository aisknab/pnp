# Public review entrypoint

> **Current authority:** Formal reconstruction is in progress and public theorem emission is
> disabled. This document describes a June 2026 legacy review-navigation coordinate, not a theorem
> gate. See [`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json)
> and [`docs/FORMAL_RECONSTRUCTION.md`](./docs/FORMAL_RECONSTRUCTION.md).

Legacy coordinate:

```text
PNP-PUBLIC-REVIEW-ENTRYPOINT-2026-06-27-01
```

Machine-readable manifest:

```text
PUBLIC_REVIEW.json
```

Checker:

```bash
node pcc-public-review-entrypoint0.mjs --json
```

The historical reviewer handoff for this legacy coordinate is:

```text
release/PUBLIC_REVIEW_HANDOFF.md
```

This root document is a navigation surface for legacy review records. It is not current status or a
theorem-activation surface.

## Legacy boundary recorded by this coordinate

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Current reviewer commands

```bash
npm ci
npm run check
npm test
npm run pnp:verify
```

`npm run pnp:verify` verifies the current formal-reconstruction boundary and writes:

```text
artifacts/pnp-verify-all/latest-verdict.json
```

## Standalone legacy non-activation audits

```bash
node pcc-public-review-entrypoint0.mjs --json
node pcc-public-review-handoff0.mjs --json
node pcc-public-review-boundary0.mjs --json
node pcc-public-surface-baseline0.mjs --json
node pcc-historical-report-supersession0.mjs --json
node pcc-historical-theorem-anchors0.mjs --json
node pcc-direct-binding-index0.mjs --json
node scripts/verify-section22-direct-bindings.mjs --json
```

## Bound surfaces

```text
publicReviewHandoffCoordinate = PNP-PUBLIC-REVIEW-HANDOFF-2026-06-27-01
publicReviewBoundaryCoordinate = PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01
publicSurfaceBaseline = PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01
historicalReportSanitizedCoordinate = PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01
historicalTheoremAnchorsCoordinate = PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01
directBindingIndexCoordinate = PNP-DIRECT-BINDING-INDEX-2026-06-27-01
section22DirectBindingRunnerCoordinate = PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01
```

## Scope

```text
publicReviewEntrypointReady = true
rootEntryDocumentReady = true
handoffSurfaceBound = true
oneCommandVerifierVisible = true
directTheoremEmissionAllowedByEntrypoint = false
```

## Non-claims

This entrypoint does not activate public theorem emission.
This entrypoint does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This entrypoint delegates reviewer procedure to the status-bound public-review handoff.
This entrypoint keeps historical theorem-emission artifacts fenced by the current sanitized public-review boundary.
