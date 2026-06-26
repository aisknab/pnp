# Semantic kernel hardening - phase 46

Phase 45 represented an empty pending findings registry for external-review artifacts.

Phase 46 adds a signed-findings validation gate for the next coordinate:

```text
ExternalReview.SignedFindings
```

This phase does **not** supply or claim any signed external-review finding. It binds the schema and an exact pending empty bundle so future signed findings have a strict coordinate and acceptance cannot be forged by caller-supplied readiness fields.

## New checker

```text
CheckSignedExternalReviewFindings0
```

The checker requires:

```text
CheckExternalReviewFindingsRegistry0 = accept
```

The predecessor must still expose:

```text
externalReviewSignedFindingsReady = false
externalReviewAcceptanceReady = false
Release.UnrestrictedFinalSoundness = blocked
ExternalReview.Acceptance = blocked
publicTheoremEmissionAllowed = false
activeFinalNodeIds = []
```

## Signed finding schema

The represented schema is:

```text
SignedExternalReviewFindingSchema0
```

Allowed finding kinds are:

```text
ExternalReviewAcceptanceFinding0
ExternalReviewRejectionFinding0
ExternalReviewRevisionRequestFinding0
```

Required finding fields are:

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

## Pending bundle

The represented bundle is intentionally empty:

```text
SignedExternalReviewFindingsBundle0
registryStatus = pending-signed-findings
signedFindingCount = 0
acceptanceFindingCount = 0
signedExternalReviewFindingsReady = false
externalReviewAcceptanceReady = false
externalReviewAcceptanceReleased = false
externalReviewAcceptanceNotClaimed = true
```

The checker rejects forged signed-acceptance bundles and rejects caller-supplied readiness assertions.

## Current blocker state

Phase 46 keeps the release gate blocked on:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

The checker keeps:

```text
publicTheoremEmissionReady = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
```

## Verification

The dedicated workflow is:

```text
.github/workflows/external-review-signed-findings.yml
```

It runs:

```bash
node --check pcc-external-review-signed-findings0.mjs
node --test test/pcc-external-review-signed-findings0.test.mjs
```

## Next step

The next release-layer work should bind actual signed finding files, if they exist. Without signed findings and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.