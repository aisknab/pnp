# Public review entrypoint artifacts

The public review entrypoint checker writes its generated verdict here:

```text
artifacts/public-review-entrypoint/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-review-entrypoint0.mjs --json
```

The checker validates the root reviewer navigation surface:

```text
PUBLIC_REVIEW.json
PUBLIC_REVIEW.md
release/PUBLIC_REVIEW_HANDOFF.json
release/PUBLIC_REVIEW_BOUNDARY.json
PNP_STATUS.json
```

It confirms that the root entrypoint points to the status-bound public-review handoff and remains non-activating:

```text
publicReviewEntrypointReady = true
rootEntryDocumentReady = true
handoffSurfaceBound = true
oneCommandVerifierVisible = true
directTheoremEmissionAllowedByEntrypoint = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
