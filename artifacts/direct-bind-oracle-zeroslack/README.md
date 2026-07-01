# O direct-binding gap seed artifacts

The O direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-oracle-zeroslack/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-oracle-zeroslack0.mjs --json
```

The checker validates the O theorem-ledger row as a complexity-and-gap transition surface:

```text
sourceLabel = O
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `O` row to current rank-parametric oracle, ZeroSlack, residual-band minimization, complexity implication ledger, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
