# Report theorem inventory artifacts

The report theorem inventory checker writes its generated verdict here:

```text
artifacts/report-theorem-inventory/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-report-theorem-inventory0.mjs --json
```

The checker validates:

```text
report-bindings/REPORT_THEOREM_INVENTORY.json
report-bindings/REPORT_THEOREM_BINDINGS.json
report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json
PNP_STATUS.json
```

It inventories the historical report Section 22 theorem-ledger rows and rejects public theorem activation, exhaustive coverage overclaims, reordered inventory entries, inventory entries with theorem-emission effects, binding-ledger theorem discharge, and missing status/policy coordinates.

The inventory is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
