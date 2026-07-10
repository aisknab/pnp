# Semantic kernel hardening - phase 52

> **Historical assertion-checker record:** This phase and its retired workflow describe a June 2026
> release-policy experiment. It is not current theorem-status authority or a current release plan.
> See [the formal reconstruction status](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [the reconstruction notice](FORMAL_RECONSTRUCTION.md).

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

## Historical next step

The recorded next step was to bind reviewer key material and signed review-finding files if supplied.
That step is not part of the current formal blocker inventory or release plan.
