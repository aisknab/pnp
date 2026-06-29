# Report theorem coverage matrix artifacts

The report theorem coverage matrix checker writes its generated verdict here:

```text
artifacts/report-theorem-coverage-matrix/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-report-theorem-coverage-matrix0.mjs --json
```

The checker validates:

```text
report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json
report-bindings/REPORT_THEOREM_INVENTORY.json
report-bindings/REPORT_THEOREM_BINDINGS.json
report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json
PNP_STATUS.json
```

It checks exact coverage-row ordering, inventory linkage, source-label alignment, evidence-file existence, release-critical boundary coverage for `Final` and `PACK`, and non-activation flags.

The matrix is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
