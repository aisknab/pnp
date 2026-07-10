# Public theorem emission preflight

> **Superseded release-policy record:** This June 2026 preflight records a historical
> assertion-checker denial boundary. It is not current theorem-status authority, and its
> release-policy blockers are not the current formal blocker inventory. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-PUBLIC-THEOREM-EMISSION-PREFLIGHT-2026-06-27-01
```

Machine-readable manifest:

```text
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json
```

Checker:

```bash
node pcc-public-theorem-emission-preflight0.mjs --json
```

This preflight accepted only the historical theorem-emission-denied state. It is not a
theorem-activation surface.

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

## Historical preflight state

```text
publicTheoremEmissionPreflightReady = true
publicTheoremEmissionPreflightPassed = false
publicTheoremEmissionDenied = true
finalTheoremReadyByPreflight = false
releaseBlockerClearanceAccepted = false
externalReviewAcceptanceClaimed = false
unrestrictedFinalSoundnessClearanceAccepted = false
publicReviewBoundaryNonActivating = true
blockedByRemainingBlockers = true
preflightTransitionRequiresFuturePR = true
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

## Required blocked ladder nodes

```text
UnrestrictedFinalSoundnessRepresented -> Release.UnrestrictedFinalSoundness
InternalTheoremActivationCandidate -> Release.UnrestrictedFinalSoundness
PublicTheoremEmissionCandidate -> ExternalReview.Acceptance
```

## Required activation-blocking gaps

```text
GAP-001-UnrestrictedFinalSoundness -> Release.UnrestrictedFinalSoundness
GAP-002-ExternalReviewAcceptance -> ExternalReview.Acceptance
GAP-003-BoundedSmallModelsNotUniformProof -> Release.UnrestrictedFinalSoundness
GAP-004-FiniteToUnboundedUniformity -> Release.UnrestrictedFinalSoundness
```

## Non-claims

This preflight does not activate public theorem emission.
This preflight does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This preflight intentionally did not pass in the recorded state.
This preflight does not claim unrestricted final soundness.
This preflight does not claim independent external review acceptance.
This preflight does not mark any Section 22 theorem-ledger row as fully discharged.
