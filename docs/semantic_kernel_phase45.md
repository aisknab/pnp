# Semantic kernel hardening - phase 45

Phase 44 represented the external-review request gate. It did not claim acceptance and kept the release-layer blockers in place:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

Phase 45 adds a findings-registry gate for signed external-review findings.

## New checker

```text
CheckExternalReviewFindingsRegistry0
```

The checker requires:

```text
CheckExternalReviewGate0 = accept
```

The predecessor must still have:

```text
ExternalReview.Acceptance = blocked
Release.UnrestrictedFinalSoundness = blocked
publicTheoremEmissionAllowed = false
activeFinalNodeIds = []
```

## Findings registry

The represented registry is:

```text
ExternalReviewFindingsRegistry0
```

It is intentionally pending and empty:

```text
registryStatus = pending-signed-findings
signedFindingCount = 0
acceptanceFindingCount = 0
rejectionFindingCount = 0
revisionRequestFindingCount = 0
externalReviewSignedFindingsReady = false
externalReviewAcceptanceReady = false
externalReviewAcceptanceNotClaimed = true
```

The allowed future finding kinds are:

```text
ExternalReviewAcceptanceFinding0
ExternalReviewRejectionFinding0
ExternalReviewRevisionRequestFinding0
```

The required signed-finding fields are:

```text
kind
version
reviewerIdentityDigest
reviewScopeDigest
documentationCoordinate
sealedSourceCommit
sealedArtifactTag
finding
findingDigest
signatureDigest
```

## Current blocker state

Phase 45 keeps the release gate blocked on:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

The checker keeps:

```text
externalReviewSignedFindingsReady = false
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
.github/workflows/external-review-findings-registry.yml
```

It runs:

```bash
node --check pcc-external-review-findings-registry0.mjs
node --test test/pcc-external-review-findings-registry0.test.mjs
```

## Next step

The next release-layer work should bind actual signed external-review findings if they exist. Without signed acceptance and unrestricted-final-soundness release artifacts, public theorem emission remains disabled.