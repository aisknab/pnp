# Semantic kernel hardening - phase 51

Phase 50 bound the semantic shape of the external-review finding templates.

Phase 51 adds a non-activating reviewer-authentication policy coordinate:

```text
ExternalReview.SignaturePolicy
```

This phase does not add any signed finding file and does not claim external review acceptance.

## New checker

```text
CheckExternalReviewSignaturePolicy0
```

The checker depends on:

```text
CheckExternalReviewTemplateShape0 = accept
```

## Policy

The policy records the future artifact classes and digest boundaries needed before an external-review finding can be treated as review evidence. It keeps all counts at zero:

```text
signedFindingFileCount = 0
verifiedSignatureCount = 0
acceptedSignatureCount = 0
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
node --check pcc-external-review-signature-policy0.mjs
```

## Next step

The next release-layer work should bind actual signed finding files and review-authentication material if supplied. Without signed findings and an unrestricted-final-soundness release artifact, public theorem emission remains disabled.
