# Public review boundary artifacts

The public review boundary checker writes its generated verdict here:

```text
artifacts/public-review-boundary/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-review-boundary0.mjs --json
```

The checker validates the aggregate non-activation perimeter:

```text
PNP_STATUS.json
release/RELEASE_LADDER.json
proof-obligations/GAP_LEDGER.json
report-bindings/HISTORICAL_REPORT_SUPERSESSION.json
report-bindings/HISTORICAL_THEOREM_ANCHORS.json
pcc-public-surface-baseline0.mjs
```

It confirms that the public-review boundary is ready but non-activating:

```text
publicReviewBoundaryReady = true
publicTheoremEmissionAllowedByBoundary = false
finalTheoremReadyByBoundary = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
