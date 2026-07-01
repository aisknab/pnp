# Packet direct-binding gap seed artifacts

The Packet direct-binding gap seed checker writes its generated verdict here:

```text
artifacts/direct-bind-packet-selector-seeds/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-packet-selector-seeds0.mjs --json
```

The checker validates the Packet theorem-ledger row as a gap-transition surface:

```text
sourceLabel = Packet
closureStatus = blocked-by-unrestricted-final-soundness
blockingGaps = [
  "GAP-001-UnrestrictedFinalSoundness",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `Packet` row to current pair, balanced-triple, and full-span packet extraction into faithful selector seeds, payload preservation, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
