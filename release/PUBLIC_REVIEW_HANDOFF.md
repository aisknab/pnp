# Public review handoff

> **Superseded reviewer handoff:** This June 2026 handoff describes a historical assertion-checker
> review perimeter. It is not current theorem-status authority or a current release gate. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

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

This handoff gave reviewers one entry surface for the historical non-activation perimeter. It records
the verifier command and standalone audit surfaces used by that checker stack.

It is not a theorem-activation surface.

## Historical boundary

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Historical audit command

```bash
npm ci
npm run pnp:verify
```

On current `main`, `npm run pnp:verify` checks the formal-reconstruction boundary. Historical
verdict fields produced by the command remain assertion-checker evidence only. The command writes:

```text
artifacts/pnp-verify-all/latest-verdict.json
```

## Standalone historical boundary commands

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
This handoff does not determine current status. The formal-reconstruction status keeps all historical
theorem-emission artifacts subordinate.
