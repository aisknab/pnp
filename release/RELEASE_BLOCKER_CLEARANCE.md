# Release blocker clearance protocol

Current coordinate:

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

This document records the current protocol for clearing the release blockers. It is not a theorem-activation surface.

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

## Current clearance state

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

Current state:

```text
not-cleared
```

Required future evidence:

```text
Accepted unrestricted final soundness checker covering the non-seed, non-bounded statement for all SAT input sizes under polynomial-time generation.
```

This blocker may be removed from `remainingBlockers` only after an accepted release-ladder transition records that future evidence.

### ExternalReview.Acceptance

Current state:

```text
not-cleared
```

Required future evidence:

```text
Accepted independent external-review evidence recorded as an explicit release transition.
```

This blocker may be removed from `remainingBlockers` only after an accepted release-ladder transition records that future evidence.

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
