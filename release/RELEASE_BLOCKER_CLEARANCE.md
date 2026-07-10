# Release blocker clearance protocol

> **Superseded release-policy record:** This June 2026 protocol records historical
> assertion-checker blockers. External review is not a current formal blocker or mathematical
> premise. Current obligations are listed in
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json); see
> also [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-RELEASE-BLOCKER-CLEARANCE-2026-06-27-01
```

Machine-readable manifest:

```text
release/RELEASE_BLOCKER_CLEARANCE.json
```

Checker:

```bash
node pcc-release-blocker-clearance0.mjs --json
```

This document recorded the historical protocol for clearing its release-policy blockers. It is not
a theorem-activation surface.

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

## Historical clearance state

```text
clearanceProtocolReady = true
releaseBlockersStillActive = true
releaseBlockerClearanceAccepted = false
unrestrictedFinalSoundnessClearanceAccepted = false
externalReviewClearanceAccepted = false
publicTheoremEmissionAllowedByClearance = false
finalTheoremReadyByClearance = false
blockedTransitionOnly = true
clearanceTransitionRequiresFuturePR = true
```

## Clearance rules

### Release.UnrestrictedFinalSoundness

Recorded state:

```text
not-cleared
```

Evidence required by the historical protocol:

```text
Accepted unrestricted final soundness checker covering the non-seed, non-bounded statement for all SAT input sizes under polynomial-time generation.
```

The historical protocol allowed this blocker to be removed only after an accepted release-ladder
transition recorded that evidence.

### ExternalReview.Acceptance

Recorded state:

```text
not-cleared
```

Evidence required by the historical protocol:

```text
Accepted independent external-review evidence recorded as an explicit release transition.
```

The historical protocol allowed this blocker to be removed only after an accepted release-ladder
transition recorded that evidence.

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

This protocol does not activate public theorem emission.
This protocol does not clear `Release.UnrestrictedFinalSoundness` or `ExternalReview.Acceptance`.
This protocol does not claim unrestricted final soundness.
This protocol does not claim independent external review acceptance.
This protocol does not mark any Section 22 theorem-ledger row as fully discharged.
