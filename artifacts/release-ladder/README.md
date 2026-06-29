# Release ladder artifacts

The release ladder checker writes its generated verdict here:

```text
artifacts/release-ladder/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-release-ladder0.mjs --json
```

The checker validates:

```text
release/RELEASE_LADDER.json
PNP_STATUS.json
```

It ensures that release statuses are ordered, dependencies point backward, current blocked states remain blocked, and public theorem emission remains disabled while the listed blockers remain active.

The release ladder is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
