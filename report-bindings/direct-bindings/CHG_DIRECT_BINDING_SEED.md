# CHG direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-CHG-CHARGE-LEDGER-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-charge-ledger0.mjs --json
```

This seed binds the historical Section 22 `CHG` theorem-ledger row to the current charge-ledger, ownership, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
chgDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalCHGTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers global charge-ledger representation, materializer ownership representation, exact size-equation surfaces, and the current charge-soundness activation boundary. It does not yet flip the `CHG` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full charge-soundness discharge artifact only after the checker, proof artifact, negative tests, and gap-status transition are all represented.
