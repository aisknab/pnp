# BN4 direct-binding gap seed artifacts

The BN4 direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-bn4-activation/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-bn4-activation0.mjs --json
```

The checker validates the BN4 theorem-ledger row as a gap-transition surface:

```text
sourceLabel = BN4
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `BN4` row to current activation-exact cancellation by active minimal-consumer antichains, same-key cancellation, integer mass ledger, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
