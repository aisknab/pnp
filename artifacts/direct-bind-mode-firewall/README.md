# Mode direct-binding seed artifacts

The Mode direct-binding seed checker writes its generated verdict here:

```text
artifacts/direct-bind-mode-firewall/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-mode-firewall0.mjs --json
```

The checker validates:

```text
report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json
report-bindings/REPORT_THEOREM_INVENTORY.json
report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json
report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json
kernel/PNP_MINIMAL_KERNEL.json
proof-obligations/OBLIGATION_LEDGER.json
proof-obligations/GAP_LEDGER.json
PNP_STATUS.json
```

It binds the historical `Mode` theorem-ledger row to current full-to-quotient projection, mode-firewall, transfer-identity, minimal-kernel, proof-obligation, and gap-ledger surfaces while rejecting public theorem activation, direct-binding completion overclaims, Mode row drift, missing kernel rules, missing proof-obligation linkage, and missing status coordinate.

The seed is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
