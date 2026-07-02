# External review status artifacts

The external review status checker writes its generated verdict here:

```text
artifacts/external-review-status/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-external-review-status0.mjs --json
```

The checker validates the current external-review non-acceptance surface:

```text
review/EXTERNAL_REVIEW_STATUS.json
review/EXTERNAL_REVIEW_STATUS.md
EXTERNAL_REVIEW_STATUS.md
PNP_STATUS.json
review/PUBLIC_REVIEW_CHECKLIST.json
release/RELEASE_LADDER.json
proof-obligations/GAP_LEDGER.json
```

It confirms that no independent external review acceptance is claimed and that the external-review blocker remains active:

```text
externalReviewStatusReady = true
externalReviewAcceptanceClaimed = false
independentReviewAcceptanceConfirmed = false
noIndependentReviewerConfirmed = true
externalReviewBlockerStillActive = true
substantiveFeedbackIsAcceptance = false
publicTheoremEmissionAllowedByExternalReview = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
