# R direct-binding gap seed artifacts

The R direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-selector-realizer/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-selector-realizer0.mjs --json
```

The checker validates the R theorem-ledger row as a gap-transition surface:

```text
sourceLabel = R
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `R` row to current selector realizers, typed bottom outputs, strict charge surplus, gain-only public interface, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
