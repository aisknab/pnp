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

The checker validates that the root historical report files are represented as historical theorem-emission surfaces:

```text
canonical_proof_report.tex
canonical_proof_report.pdf
```

and that the current successor status boundary supersedes that historical prose for active public-release state.

The audit is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
