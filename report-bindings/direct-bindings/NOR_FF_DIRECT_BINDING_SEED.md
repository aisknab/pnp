# NOR/FF direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-NOR-FF-FRONTIER-FAITHFUL-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/NOR_FF_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-frontier-faithful0.mjs --json
```

This seed binds the historical Section 22 `NOR/FF` theorem-ledger row to the current strong neutral overlay, FF-LOSS, frontier-faithful comparison, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
norFfDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalNORFFTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers strong neutral overlay representation, FF-LOSS representation, frontier-faithful comparison representation, checker-hardening representation, and the current NOR/FF activation boundary. It does not yet flip the `NOR/FF` row in the coverage matrix to `directCheckerBindingComplete = true`.

## Boundary

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

The next direct-binding PR for this row should add a full frontier-faithful comparison discharge artifact only after the checker, proof artifact, negative tests, strong-neutral-overlay audit, FF-LOSS audit, frontier-faithful comparison audit, and release-boundary transition are all represented.
