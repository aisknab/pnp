# Final theorem boundary seed artifacts

The Final theorem boundary seed checker writes its generated verdict here:

```text
artifacts/direct-bind-final-theorem-boundary/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-final-theorem-boundary0.mjs --json
```

The checker validates the Final theorem-ledger row as a release-critical boundary surface:

```text
sourceLabel = Final
closureStatus = release-boundary-blocked
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-002-ExternalReviewAcceptance"
]
```

It binds the historical `Final` row to the current release ladder, theorem-binding ledger, gap ledger, status boundary, coverage matrix, closure plan, and non-activation surfaces.

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
