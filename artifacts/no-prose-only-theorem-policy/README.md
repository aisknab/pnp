# No prose-only theorem policy artifacts

The no-prose-only theorem policy checker writes its generated verdict here:

```text
artifacts/no-prose-only-theorem-policy/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-no-prose-only-theorem-policy0.mjs --json
```

The checker validates:

```text
report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json
report-bindings/REPORT_THEOREM_BINDINGS.json
proof-obligations/OBLIGATION_LEDGER.json
proof-obligations/GAP_LEDGER.json
PNP_STATUS.json
```

It ensures the release-critical theorem spine is bound to checker/proof/test surfaces and refuses prose-only theorem activation, public theorem emission, full report theorem inventory overclaims, and release-blocker clearance.

The policy is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
