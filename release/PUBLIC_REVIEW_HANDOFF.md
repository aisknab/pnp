# Public review handoff

Current coordinate:

```text
PNP-PUBLIC-REVIEW-HANDOFF-2026-06-27-01
```

Machine-readable manifest:

```text
release/PUBLIC_REVIEW_HANDOFF.json
```

Checker:

```bash
node pcc-public-review-handoff0.mjs --json
```

This handoff gives reviewers one current entry surface for the non-activation public-review perimeter. It points at the ordinary verifier command and the major standalone audit surfaces.

It is not a theorem-activation surface.

## Current boundary

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Primary command

```bash
npm ci
npm run pnp:verify
```

`npm run pnp:verify` writes:

```text
artifacts/pnp-verify-all/latest-verdict.json
```

## Standalone boundary commands

```bash
node pcc-public-review-boundary0.mjs --json
node pcc-public-surface-baseline0.mjs --json
node pcc-historical-report-supersession0.mjs --json
node pcc-historical-theorem-anchors0.mjs --json
node pcc-direct-binding-index0.mjs --json
node scripts/verify-section22-direct-bindings.mjs --json
```

## What this handoff binds

```text
publicReviewBoundaryCoordinate = PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01
publicSurfaceBaseline = PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01
historicalReportSupersessionCoordinate = PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01
historicalReportSanitizedCoordinate = PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01
historicalTheoremAnchorsCoordinate = PNP-HISTORICAL-THEOREM-ANCHORS-2026-06-27-01
directBindingIndexCoordinate = PNP-DIRECT-BINDING-INDEX-2026-06-27-01
section22DirectBindingRunnerCoordinate = PNP-SECTION22-DIRECT-BINDING-RUNNER-2026-06-27-01
releaseLadderCoordinate = PNP-RELEASE-LADDER-2026-06-27-01
gapLedgerCoordinate = PNP-GAP-LEDGER-2026-06-27-01
```

## Scope

```text
publicReviewHandoffReady = true
handoffDocReady = true
publicReviewBoundaryBound = true
oneCommandVerifierBound = true
historicalReportSanitized = true
publicSurfaceBaselineBound = true
section22DirectBindingSurfacesBound = true
directTheoremEmissionAllowedByHandoff = false
```

## Non-claims

This handoff does not activate public theorem emission.
This handoff does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This handoff does not mark any Section 22 theorem-ledger row as fully discharged.
This handoff keeps historical theorem-emission artifacts fenced by the current sanitized public-review boundary.
