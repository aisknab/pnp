# Semantic kernel hardening - phase 49

Phase 48 bound the current empty signed-finding intake directory with a SHA256 ledger.

Phase 49 adds digest-bound templates for future signed external-review findings:

```text
ExternalReview.SignedFindingTemplates
```

This phase does **not** add any signed finding file and does **not** claim external review acceptance.

## New checker

```text
CheckExternalReviewFindingTemplateLedger0
```

The checker depends on:

```text
CheckExternalReviewFindingFileHashLedger0 = accept
```

## Templates

```text
external-review/templates/acceptance-finding.template.json
external-review/templates/rejection-finding.template.json
external-review/templates/revision-request-finding.template.json
external-review/templates/SHA256SUMS
```

The template hashes are:

```text
110d35baea012ebf8bbef17314bb289ca949edfa03f8fa7346f7a68232348f14  external-review/templates/acceptance-finding.template.json
f97527a3ab8660d961707ecdfe8f39a90a9d3ad2bb758a872903f62172ac706e  external-review/templates/rejection-finding.template.json
9d702f97d85502e271716c444eda47fcf662db57c09d210bd4788074747c0aa3  external-review/templates/revision-request-finding.template.json
```

The templates are not findings. They are inert examples for future digest-bound review artifacts and cannot activate the release gate.

## Release boundary

The checker keeps:

```text
externalReviewSignedFindingTemplatesReady = true
externalReviewSignedFindingFilesReady = false
externalReviewAcceptanceReady = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
sealedReleaseNotOverwritten = true
```

The release gate remains blocked on:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

## Verification

```bash
sha256sum -c external-review/templates/SHA256SUMS
node --check pcc-external-review-finding-template-ledger0.mjs
node --test test/pcc-external-review-finding-template-ledger0.test.mjs
```

## Next step

The next release-layer work should bind actual signed finding files if they are supplied. Without signed findings and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.
