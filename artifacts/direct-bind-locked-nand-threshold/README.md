# G direct-binding seed artifacts

The G direct-binding seed checker writes its generated verdict here:

```text
artifacts/direct-bind-locked-nand-threshold/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-direct-bind-locked-nand-threshold0.mjs --json
```

The checker validates the G theorem-ledger row as a locked-NAND seed surface:

```text
sourceLabel = G
closureStatus = direct-binding-seed-upgrade-needed
blockingGaps = [
  "GAP-003-BoundedSmallModelsNotUniformProof",
  "GAP-004-FiniteToUnboundedUniformity"
]
```

It binds the historical `G` row to current locked NAND SAT threshold small-model evidence, macro truth-table surface, baseline/threshold row, residual-slack-at-most-four surface, complexity implication ledger, finite-to-unbounded audit, gap-ledger, theorem inventory, coverage matrix, closure plan, and non-activation surfaces.

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
