# Semantic kernel hardening - phase 52

Phase 51 added a non-activating external-review signature policy.

Phase 52 adds an empty reviewer verification-key registry coordinate:

```text
ExternalReview.VerificationKeyRegistry
```

This phase does not add reviewer keys, signed findings, or external review acceptance.

## New checker

```text
CheckExternalReviewVerificationKeyRegistry0
```

The checker depends on:

```text
CheckExternalReviewSignaturePolicy0 = accept
```

## Registry

The registry is intentionally empty:

```text
registryStatus = pending-reviewer-keys
verificationKeyCount = 0
trustedReviewerKeyCount = 0
revokedReviewerKeyCount = 0
externalReviewVerificationKeysReady = false
externalReviewVerifiedSignaturesReady = false
externalReviewAcceptanceReady = false
externalReviewAcceptanceNotClaimed = true
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
node --check pcc-external-review-verification-key-registry0.mjs
```

## Next step

The next release-layer work should bind actual reviewer key material and signed review-finding files if supplied. Without signed findings and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.
