# Semantic kernel hardening - phase 47

Phase 46 represented the signed external-review finding schema and an exact pending empty bundle. It did not supply or claim any signed finding.

Phase 47 adds a file-intake coordinate for future digest-bound signed external-review findings:

```text
ExternalReview.SignedFindingFiles
```

This phase does **not** add any signed finding file and does **not** claim external review acceptance.

## New checker

```text
CheckExternalReviewFindingFiles0
```

The checker requires:

```text
CheckSignedExternalReviewFindings0 = accept
```

The predecessor must still expose:

```text
signedExternalReviewFindingsReady = false
externalReviewAcceptanceReady = false
Release.UnrestrictedFinalSoundness = blocked
ExternalReview.Acceptance = blocked
publicTheoremEmissionAllowed = false
activeFinalNodeIds = []
```

## Intake directory

```text
external-review/findings/
```

The directory currently contains only an empty manifest and README:

```text
external-review/findings/MANIFEST.json
external-review/findings/README.md
```

The manifest is intentionally empty:

```text
signedFindingFileCount = 0
acceptanceFindingFileCount = 0
rejectionFindingFileCount = 0
revisionRequestFindingFileCount = 0
externalReviewSignedFindingFilesReady = false
externalReviewAcceptanceReady = false
externalReviewAcceptanceNotClaimed = true
```

Future signed findings must be represented by successor coordinates before they can affect any release gate.

## Current blocker state

Phase 47 keeps the release gate blocked on:

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
.github/workflows/external-review-finding-files.yml
```

It runs:

```bash
node --check pcc-external-review-finding-files0.mjs
node --test test/pcc-external-review-finding-files0.test.mjs
```

## Next step

The next release-layer work should bind actual signed finding files, if they are supplied. Without signed findings and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.
