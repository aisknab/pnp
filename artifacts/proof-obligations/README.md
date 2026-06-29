# Proof obligation ledger artifacts

The proof obligation ledger checker writes its generated verdict here:

```text
artifacts/proof-obligations/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-proof-obligation-ledger0.mjs --json
```

The checker validates:

```text
proof-obligations/OBLIGATION_LEDGER.json
```

It checks the non-activation boundary, exact obligation ordering, dependency ordering, status vocabulary, source/test file existence, and computes SHA256 digests for all declared source and test files.

The proof obligation ledger is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
