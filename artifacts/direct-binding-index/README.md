# Section 22 direct-binding index artifacts

The Section 22 direct-binding index checker writes its generated verdict here:

```text
artifacts/direct-binding-index/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-binding-index0.mjs --json
```

The checker validates that all 27 historical Section 22 theorem-ledger rows have an executable surface in the successor stack:

```text
inventory row
coverage row
closure-plan row
direct-binding manifest
checker file
test file
```

The index is not a release activation. It preserves the current boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
