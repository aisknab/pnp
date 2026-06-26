# Semantic kernel hardening - phase 48

Phase 48 binds the current external-review finding intake files to an explicit SHA256 ledger.

## Coordinate

```text
ExternalReview.SignedFindingFileHashes
```

## New checker

```text
CheckExternalReviewFindingFileHashLedger0
```

The checker depends on:

```text
CheckExternalReviewFindingFiles0 = accept
```

## Ledger

```text
external-review/findings/SHA256SUMS
```

Current entries:

```text
2f8ecf1ca93e6f94db967b7808948e97a330850bda7ee4211defcc151d2e5869  external-review/findings/MANIFEST.json
0243c7fe3c77968a5000cfdc471c5c651e9de790285e990464d06518510f4edb  external-review/findings/README.md
```

The intake remains empty:

```text
signedFindingFileCount = 0
acceptanceFindingFileCount = 0
externalReviewSignedFindingFileHashesReady = true
externalReviewSignedFindingFilesReady = false
externalReviewAcceptanceReady = false
```

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
sha256sum -c external-review/findings/SHA256SUMS
node --check pcc-external-review-finding-file-hash-ledger0.mjs
node --test test/pcc-external-review-finding-file-hash-ledger0.test.mjs
```
