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

The checker validates:

```text
report-bindings/HISTORICAL_THEOREM_ANCHORS.json
report-bindings/HISTORICAL_THEOREM_ANCHORS.md
report-bindings/REPORT_THEOREM_BINDINGS.json
canonical_proof_report.tex
PNP_STATUS.json
```

It ensures that theorem-binding anchors remain represented after the current root report was sanitized, without turning the anchor index into a public theorem-emission surface.

The checker is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
