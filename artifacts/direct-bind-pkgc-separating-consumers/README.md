# PkgC direct-binding gap seed artifacts

The PkgC direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-pkgc-separating-consumers/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-pkgc-separating-consumers0.mjs --json
```

The checker validates the PkgC theorem-ledger row as a gap-transition surface:

```text
sourceLabel = PkgC
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `PkgC` row to current request traces, full-restoration universes, nonsingleton separating-consumer routing, quotient-to-full key preservation, singletonization, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
