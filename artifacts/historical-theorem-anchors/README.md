# Historical theorem anchor artifacts

The historical theorem anchor checker writes its generated verdict here:

```text
artifacts/historical-theorem-anchors/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-historical-theorem-anchors0.mjs --json
```

The checker validates that the sanitized theorem-anchor index contains exactly the anchor strings referenced by:

```text
report-bindings/REPORT_THEOREM_BINDINGS.json
```

The anchor index is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
