# External review verification keys

This directory is the intake coordinate for future external-review verification keys.

Current status:

```text
verificationKeyFileCount = 0
trustedReviewerKeyFileCount = 0
revokedReviewerKeyFileCount = 0
externalReviewVerificationKeyFilesReady = false
externalReviewVerificationKeysReady = false
externalReviewVerifiedSignaturesReady = false
externalReviewAcceptanceReady = false
publicTheoremEmissionAllowed = false
```

No reviewer verification key is supplied by this directory. A future reviewer key must be added as a digest-bound file and represented by a successor checker before it can be used to verify any external-review finding.

The sealed `7072f8d` source/checker release and sealed artifact release are not modified by this directory.
