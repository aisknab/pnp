# RW direct-binding gap seed artifacts

The RW direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-residual-witness/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-residual-witness0.mjs --json
```

The checker validates the RW theorem-ledger row as a gap-transition surface:

```text
sourceLabel = RW
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `RW` row to current MuBridge, SpanPolicy, SaturatePositive, RankWF, BCELReady, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
