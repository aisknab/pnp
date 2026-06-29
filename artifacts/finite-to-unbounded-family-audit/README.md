# Finite-to-unbounded family audit artifacts

The finite-to-unbounded family audit checker writes its generated verdict here:

```text
artifacts/finite-to-unbounded-family-audit/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-finite-to-unbounded-family-audit0.mjs --json
```

The checker validates:

```text
proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json
proof-obligations/GAP_LEDGER.json
```

It keeps the finite-to-unbounded uniformity question explicit and refuses to treat bounded small-model evidence as a proof for all SAT input sizes.

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
