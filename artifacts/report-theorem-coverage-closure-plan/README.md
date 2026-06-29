# Report theorem coverage closure plan artifacts

The report theorem coverage closure plan checker writes its generated verdict here:

```text
artifacts/report-theorem-coverage-closure-plan/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-report-theorem-coverage-closure-plan0.mjs --json
```

The checker validates:

```text
report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json
report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json
PNP_STATUS.json
```

It checks exact closure-row ordering, coverage-row alignment, allowed closure statuses, release-critical blocking for `Final` and `PACK`, unrestricted-final-soundness blocking for uniformity rows, evidence-file existence, and non-activation flags.

The closure plan is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
