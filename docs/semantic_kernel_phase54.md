# Semantic kernel hardening - phase 54

Phase 53 added the external-review reviewer-key file intake directory:

```text
external-review/keys/
```

Phase 54 binds the current empty key-intake files to an explicit SHA256 ledger:

```text
ExternalReview.VerificationKeyFileHashes
```

This phase does **not** add reviewer keys, signed findings, verified signatures, or external review acceptance.

## New checker

```text
CheckExternalReviewVerificationKeyFileHashLedger0
```

The checker depends on:

```text
CheckExternalReviewVerificationKeyFiles0 = accept
```

The predecessor must still expose:

```text
externalReviewVerificationKeyFilesReady = false
externalReviewVerificationKeysReady = false
externalReviewVerifiedSignaturesReady = false
externalReviewAcceptanceReady = false
Release.UnrestrictedFinalSoundness = blocked
ExternalReview.Acceptance = blocked
publicTheoremEmissionAllowed = false
activeFinalNodeIds = []
```

## Hash ledger

The ledger is:

```text
external-review/keys/SHA256SUMS
```

It binds the current empty key-intake files:

```text
b2859ad352602aedb407d73d915e39f83bdd2968f8021352a244ccdeda4ed2d3  external-review/keys/MANIFEST.json
17630eefbe0ae41b4178514014eed9f8e666660ff4dd7b018b995d8125942712  external-review/keys/README.md
```

The represented hash ledger records:

```text
entryCount = 2
verificationKeyFileCount = 0
trustedReviewerKeyFileCount = 0
revokedReviewerKeyFileCount = 0
externalReviewVerificationKeyFileHashesReady = true
externalReviewVerificationKeyFilesReady = false
externalReviewVerificationKeysReady = false
externalReviewVerifiedSignaturesReady = false
externalReviewAcceptanceReady = false
externalReviewAcceptanceNotClaimed = true
```

## Current blocker state

Phase 54 keeps the release gate blocked on:

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
sealedReleaseNotOverwritten = true
```

## Verification

The dedicated workflow is:

```text
.github/workflows/external-review-key-file-hashes.yml
```

It runs:

```bash
sha256sum -c external-review/keys/SHA256SUMS
node --check pcc-external-review-verification-key-file-hash-ledger0.mjs
node --test test/pcc-external-review-verification-key-file-hash-ledger0.test.mjs
```

## Next step

The next release-layer work should bind actual reviewer key files if they are supplied. Without reviewer keys, signed findings, verified signatures, and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.
