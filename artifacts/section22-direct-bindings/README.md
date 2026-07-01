# Section 22 direct-binding runner artifacts

The Section 22 direct-binding runner writes its generated verdict here:

```text
artifacts/section22-direct-bindings/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node scripts/verify-section22-direct-bindings.mjs --json
```

The runner consumes:

```text
report-bindings/direct-bindings/DIRECT_BINDING_INDEX.json
```

and executes every indexed row checker, plus every indexed row test unless `--skip-row-tests` is passed.

The runner is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
