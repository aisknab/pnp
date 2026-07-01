# HB direct-binding gap seed artifacts

The HB direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-hb-negative-closure/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-hb-negative-closure0.mjs --json
```

The checker validates the HB theorem-ledger row as a gap-transition surface:

```text
sourceLabel = HB
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `HB` row to current simultaneous HN-BUD rank-parametric negative closure, selector-silence induction, blocker graph acyclicity, no-circular negative closure, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
