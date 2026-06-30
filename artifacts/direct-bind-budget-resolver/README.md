# BUD direct-binding seed artifacts

The BUD direct-binding seed checker writes its generated verdict here:

```text
artifacts/direct-bind-budget-resolver/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-budget-resolver0.mjs --json
```

The checker validates:

```text
report-bindings/direct-bindings/BUD_DIRECT_BINDING_SEED.json
report-bindings/REPORT_THEOREM_INVENTORY.json
report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json
report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json
proof-obligations/OBLIGATION_LEDGER.json
proof-obligations/GAP_LEDGER.json
checker-totality/CHECKER_TOTALITY_AUDIT.json
checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json
semantic-kernel/RULE_FAMILY_COVERAGE.json
PNP_STATUS.json
```

It binds the historical `BUD` theorem-ledger row to current budget-envelope dynamic programming, active budget audit, routing, strong NoBudget sidecar, checker-hardening, proof-obligation, and gap-ledger surfaces while rejecting public theorem activation, direct-binding completion overclaims, BUD row drift, unexpected closure gaps, hardening-ledger overclaims, missing proof-obligation linkage, and missing status coordinate.

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
