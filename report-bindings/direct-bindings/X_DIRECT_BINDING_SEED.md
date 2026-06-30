# X direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-X-CRITICAL-WINDOW-ROUTING-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/X_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-critical-window-routing0.mjs --json
```

This seed binds the historical Section 22 `X` theorem-ledger row to the current CritC/Q/E/L routing, X1-X4 candidate-tower routing, route-priority, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
xDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalXTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers critical-kind routing representation, candidate-tower representation, X1-X4 failure-route representation, route-priority and checker-hardening representation, and the current X activation boundary. It does not yet flip the `X` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full critical-window routing discharge artifact only after the checker, proof artifact, negative tests, route-priority audit, and release-boundary transition are all represented.
