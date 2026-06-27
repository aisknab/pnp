# Semantic kernel hardening - phase 50

Phase 49 added digest-bound templates for future signed external-review findings.

Phase 50 binds the semantic shape of those templates:

```text
ExternalReview.SignedFindingTemplateShapes
```

This phase does **not** add any signed finding file and does **not** claim external review acceptance.

## New checker

```text
CheckExternalReviewTemplateShape0
```

The checker depends on:

```text
CheckExternalReviewFindingTemplateLedger0 = accept
```

## Template shape ledger

The shape ledger records that each template is inert and placeholder-only. The represented finding values are:

```text
accept
reject
revision-request
```

Each template must retain placeholder digest fields:

```text
reviewerIdentityDigest
reviewScopeDigest
findingDigest
signatureDigest
```

with:

```text
alg = SHA256
hex = <64 lowercase hex characters>
```

The ledger records:

```text
externalReviewSignedFindingTemplatesReady = true
externalReviewSignedFindingTemplateShapesReady = true
externalReviewSignedFindingFilesReady = false
externalReviewAcceptanceReady = false
externalReviewAcceptanceNotClaimed = true
```

Templates are not findings. They cannot activate the release gate.

## Release boundary

The release gate remains blocked on:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

The checker keeps:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
sealedReleaseNotOverwritten = true
```

## Verification

```bash
sha256sum -c external-review/templates/SHA256SUMS
node --check pcc-external-review-template-shape0.mjs
node --test test/pcc-external-review-template-shape0.test.mjs
```

## Next step

The next release-layer work should bind actual signed finding files if they are supplied. Without signed findings and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.
