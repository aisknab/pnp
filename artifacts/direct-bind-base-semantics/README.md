# Base direct-binding seed artifacts

The Base direct-binding seed checker writes its generated verdict here:

```text
artifacts/direct-bind-base-semantics/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-base-semantics0.mjs --json
```

The checker validates:

```text
report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json
report-bindings/REPORT_THEOREM_INVENTORY.json
report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json
report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json
semantics/nand-direct-wire-spec.json
proof-obligations/OBLIGATION_LEDGER.json
proof-obligations/GAP_LEDGER.json
PNP_STATUS.json
```

It binds the historical `Base` theorem-ledger row to the current executable NAND direct-wire semantics seed while rejecting public theorem activation, direct-binding completion overclaims, Base row drift, missing semantics concepts, missing proof-obligation linkage, and missing status coordinate.

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
