# Historical report supersession artifacts

The historical report supersession checker writes its generated verdict here:

```text
artifacts/historical-report-supersession/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-historical-report-supersession0.mjs --json
```

The checker validates that the current root canonical report files are sanitized status notices:

```text
canonical_proof_report.tex
canonical_proof_report.pdf
```

and that old direct theorem-emission fragments are absent from the current root report surface.

The audit remains non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
