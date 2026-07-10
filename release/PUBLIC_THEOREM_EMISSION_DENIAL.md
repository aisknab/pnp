# Public theorem-emission denial certificate

> **Superseded release-policy record:** This June 2026 certificate records a historical
> assertion-checker denial state. It is not current theorem-status authority, and its release-policy
> blockers are not the current formal blocker inventory. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

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

This certificate recorded the historical theorem-emission-denied state after its preflight. It is
not a theorem-activation surface.

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

## Historical denial state

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
