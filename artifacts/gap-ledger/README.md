# Gap ledger artifacts

The gap ledger checker writes its generated verdict here:

```text
artifacts/gap-ledger/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-gap-ledger0.mjs --json
```

The checker validates:

```text
proof-obligations/GAP_LEDGER.json
```

It checks the non-activation boundary, exact gap ordering, allowed status vocabulary, activation-blocker linkage, source evidence file existence, and SHA256 digests for all declared evidence files.

The gap ledger is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
