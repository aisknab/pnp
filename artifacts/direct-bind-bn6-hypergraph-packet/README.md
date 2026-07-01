# BN6 direct-binding gap seed artifacts

The BN6 direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-bn6-hypergraph-packet/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-bn6-hypergraph-packet0.mjs --json
```

The checker validates the BN6 theorem-ledger row as a gap-transition surface:

```text
sourceLabel = BN6
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `BN6` row to current nonnegative hypergraph cellization, constant-cut rigidity, packet-collapse, packet payload preservation, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
