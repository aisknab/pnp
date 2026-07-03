# Public theorem-emission denial certificate

Current coordinate:

```text
PNP-PUBLIC-THEOREM-EMISSION-DENIAL-2026-06-27-01
```

Machine-readable manifest:

```text
release/PUBLIC_THEOREM_EMISSION_DENIAL.json
```

Checker:

```bash
node pcc-public-theorem-emission-denial0.mjs --json
```

This certificate records the current theorem-emission-denied state after the public theorem-emission preflight. It is not a theorem-activation surface.

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

## Current denial state

```text
denialCertificateReady = true
publicTheoremEmissionDenied = true
publicTheoremEmissionAllowedByDenial = false
publicTheoremEmissionPreflightPassed = false
finalTheoremReadyByDenial = false
blockedByRemainingBlockers = true
releaseBlockerClearanceAccepted = false
externalReviewAcceptanceClaimed = false
unrestrictedFinalSoundnessClearanceAccepted = false
denialCertificateIsActivationSurface = false
denialTransitionRequiresFuturePR = true
```

## Denied reasons

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

## Bound surfaces

```text
publicTheoremEmissionPreflightCoordinate = PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01
releaseBlockerClearanceCoordinate = PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01
externalReviewStatusCoordinate = PNP-EXTERNAL-REVIEW-STATUS-2026-06-27-01
publicReviewChecklistCoordinate = PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01
publicReviewBoundaryCoordinate = PNP-PUBLIC-REVIEW-BOUNDARY-2026-06-27-01
releaseLadderCoordinate = PNP-RELEASE-LADDER-2026-06-27-01
gapLedgerCoordinate = PNP-GAP-LEDGER-2026-06-27-01
```

## Non-claims

This certificate does not activate public theorem emission.
This certificate does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This certificate does not pass the public theorem-emission preflight.
This certificate does not claim unrestricted final soundness.
This certificate does not claim independent external review acceptance.
This certificate does not mark any Section 22 theorem-ledger row as fully discharged.
