# Public theorem-emission status summary

Current coordinate:

```text
PNP-PUBLIC-THEOREM-EMISSION-STATUS-2026-06-27-01
```

Machine-readable manifest:

```text
release/PUBLIC_THEOREM_EMISSION_STATUS.json
```

Checker:

```bash
node pcc-public-theorem-emission-status0.mjs --json
```

This document is a compact public theorem-emission status summary. It is not a theorem-activation surface.

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

## Current status summary

```text
currentPublicEmissionState = denied
publicTheoremEmissionStatusReady = true
statusDocReady = true
statusBound = false
gateStatusBound = true
gatePassed = false
gateDenied = true
preflightPassed = false
denialCertificateReady = true
negativeTransitionsRejected = true
releaseBlockersStillActive = true
externalReviewAcceptanceClaimed = false
allActivationBlockersVisible = true
publicTheoremEmissionAllowedByStatus = false
finalTheoremReadyByStatus = false
statusSummaryIsActivationSurface = false
statusSummaryBindingRequiresFuturePR = true
```

## Bound denied-emission surfaces

```text
publicTheoremEmissionGateCoordinate = PNP-PUBLIC-THEOREM-EMISSION-GATE-2026-06-27-01
publicTheoremEmissionNegativeTransitionsCoordinate = PNP-PUBLIC-THEOREM-EMISSION-NEGATIVE-TRANSITIONS-2026-06-27-01
publicTheoremEmissionDenialCoordinate = PNP-PUBLIC-THEOREM-EMISSION-DENIAL-2026-06-27-01
publicTheoremEmissionPreflightCoordinate = PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01
releaseBlockerClearanceCoordinate = PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01
externalReviewStatusCoordinate = PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01
publicReviewChecklistCoordinate = PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01
publicReviewBoundaryCoordinate = PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01
releaseLadderCoordinate = PNP-RELEASE-LADDER-2026-06-27-01
gapLedgerCoordinate = PNP-GAP-LEDGER-2026-06-27-01
```

## Required denied reasons

```text
Status.PublicTheoremEmissionAllowedFalse
Status.FinalTheoremReadyFalse
Status.RemainingBlockersActive
ReleaseBlockerClearance.NotAccepted
ExternalReview.AcceptanceNotClaimed
ReleaseLadder.PublicTheoremEmissionCandidateBlocked
GapLedger.ActivationBlockingGapsOpen
ProofObligationLedger.ReleaseObligationsBlocked
```

## Non-claims

This status summary does not activate public theorem emission.
This status summary does not pass the public theorem-emission gate.
This status summary does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This status summary does not claim unrestricted final soundness.
This status summary does not claim independent external review acceptance.
This status summary is not yet a status-bound verification surface and requires a future binding PR.
