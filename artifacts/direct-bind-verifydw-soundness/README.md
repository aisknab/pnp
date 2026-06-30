# E direct-binding seed artifacts

The E direct-binding seed checker writes its generated verdict here:

```text
artifacts/direct-bind-verifydw-soundness/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-verifydw-soundness0.mjs --json
```

The checker validates:

```text
report-bindings/direct-bindings/E_DIRECT_BINDING_SEED.json
report-bindings/REPORT_THEOREM_INVENTORY.json
report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json
report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json
proof-obligations/OBLIGATION_LEDGER.json
proof-obligations/GAP_LEDGER.json
oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json
checker-totality/CHECKER_TOTALITY_AUDIT.json
checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json
semantic-kernel/RULE_FAMILY_COVERAGE.json
PNP_STATUS.json
```

It binds the historical `E` theorem-ledger row to current VerifyDW soundness, obligation lifecycle, checker-hardening, no-hidden-oracle, proof-obligation, and gap-ledger surfaces while rejecting public theorem activation, direct-binding completion overclaims, E row drift, no-hidden-oracle overclaims, missing proof-obligation linkage, missing GAP-005 linkage, and missing status coordinate.

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
