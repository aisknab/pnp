# BN3 direct-binding gap seed artifacts

The BN3 direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-bn3-request-envelope/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-bn3-request-envelope0.mjs --json
```

The checker validates the BN3 theorem-ledger row as a gap-transition surface:

```text
sourceLabel = BN3
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `BN3` row to current stable request systems, simultaneous finite envelopes, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
