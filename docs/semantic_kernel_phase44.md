# Semantic kernel hardening - phase 44

Phase 43 represented the unrestricted-final-soundness review packet, but deliberately left both release-layer blockers in place:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

Phase 44 represents an external-review request gate for the second coordinate:

```text
ExternalReview.Acceptance
```

This phase does **not** claim external review acceptance. It records the review-request packet and keeps public theorem emission disabled.

## New checker

```text
CheckExternalReviewGate0
```

The checker requires:

```text
CheckUnrestrictedFinalSoundnessGate0 = accept
```

The predecessor must still have:

```text
Release.UnrestrictedFinalSoundness = blocked
ExternalReview.Acceptance = blocked
publicTheoremEmissionAllowed = false
activeFinalNodeIds = []
```

## Request packet

The represented packet is:

```text
ExternalReviewRequestPacket0
```

It records the public repository, reviewer guide, reproducibility guide, sealed source tag, sealed artefact tag, and review channels. It also records that acceptance has not been supplied:

```text
externalReviewAcceptanceReady = false
externalReviewAcceptanceReleased = false
externalReviewAcceptanceNotClaimed = true
```

## External-review obligations

The request packet exposes these coordinates:

```text
ExternalReview.Scope.StatementAndClaimBoundary
ExternalReview.Reproduce.PublicReviewDocumentationCoordinate
ExternalReview.Reproduce.SealedSourceAndArtifactRelease
ExternalReview.CheckerSoundness.SemanticKernelStack
ExternalReview.CheckerSoundness.ReleaseGateStack
ExternalReview.MathematicalSoundness.UnrestrictedFinalSoundness
ExternalReview.Report.AcceptRejectWithSignedFindings
```

These are request/review obligations, not acceptance claims.

## Current blocker state

Phase 44 keeps the release gate blocked on:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

The checker keeps:

```text
externalReviewAcceptanceReady = false
externalReviewAcceptanceBlocked = true
unrestrictedFinalSoundnessReady = false
publicTheoremEmissionReady = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
```

## Verification

The dedicated workflow is:

```text
.github/workflows/external-review-gate.yml
```

It runs:

```bash
node --check pcc-external-review-gate0.mjs
node --test test/pcc-external-review-gate0.test.mjs
```

## Next step

The next release-layer work should represent actual external reviewer findings or signed acceptance/rejection artifacts. Until independent review artifacts are supplied, public theorem emission remains disabled.