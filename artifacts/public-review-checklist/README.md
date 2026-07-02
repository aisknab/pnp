# Public review checklist artifacts

The public review checklist checker writes its generated verdict here:

```text
artifacts/public-review-checklist/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-review-checklist0.mjs --json
```

The checker validates the reviewer checklist surface:

```text
review/PUBLIC_REVIEW_CHECKLIST.json
review/PUBLIC_REVIEW_CHECKLIST.md
PUBLIC_REVIEW.json
release/PUBLIC_REVIEW_HANDOFF.json
release/PUBLIC_REVIEW_BOUNDARY.json
EXTERNAL_REVIEW_STATUS.md
PNP_STATUS.json
```

It confirms that the checklist is ready, externally-review-aware, and non-activating:

```text
publicReviewChecklistReady = true
checklistDocReady = true
rootEntrypointBound = true
handoffBound = true
boundaryBound = true
externalReviewStatusBound = true
directTheoremEmissionAllowedByChecklist = false
reviewAcceptanceClaimed = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
