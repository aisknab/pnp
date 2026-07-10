# Public theorem-emission gate

> **Superseded release-policy record:** This June 2026 gate records a historical assertion-checker
> denial boundary. It is not current theorem-status authority, and its release-policy blockers are
> not the current formal blocker inventory. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-PUBLIC-THEOREM-EMISSION-GATE-2026-06-27-01
```

Machine-readable manifest:

```text
release/PUBLIC_THEOREM_EMISSION_GATE.json
```

Checker:

```bash
node pcc-public-theorem-emission-gate0.mjs --json
```

This gate historically aggregated the public theorem-emission preflight, denial certificate, and
negative-transition audit into one status-bound executable surface. It accepted only the recorded
denied state.

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

## Historical gate state

```text
publicTheoremEmissionGateReady = true
publicTheoremEmissionGatePassed = false
publicTheoremEmissionDenied = true
currentDeniedStateAccepted = true
denialCertificateBound = true
preflightBound = true
negativeTransitionsBound = true
statusBound = true
allNegativeTransitionsRejected = true
prematureActivationRejected = true
releaseBlockersStillActive = true
publicTheoremEmissionAllowedByGate = false
finalTheoremReadyByGate = false
gateIsActivationSurface = false
gateBindingRequiresFuturePR = false
```

## Bound surfaces

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

## Required denial reasons

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

## Negative transition coverage

```text
NEG-001-status-public-emission-true
NEG-002-status-final-theorem-ready
NEG-003-status-active-final-node
NEG-004-status-blockers-cleared
NEG-005-clearance-accepted
NEG-006-external-review-accepted
NEG-007-boundary-activating
NEG-008-preflight-passed
NEG-009-denial-activation-surface
```

## Non-claims

This gate does not activate public theorem emission.
This gate does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This gate does not pass the public theorem-emission preflight.
This gate does not claim unrestricted final soundness.
This gate does not claim independent external review acceptance.
This gate is status-bound but remains a denial/non-activation surface.
