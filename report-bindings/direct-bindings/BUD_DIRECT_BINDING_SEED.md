# BUD direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-BUD-BUDGET-RESOLVER-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/BUD_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-budget-resolver0.mjs --json
```

This seed binds the historical Section 22 `BUD` theorem-ledger row to the current budget-envelope dynamic program, active budget audit, routing, strong NoBudget sidecar, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
budDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalBUDTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers budget-envelope DP representation, active-budget-audit representation, routing representation, strong NoBudget sidecar representation, checker-hardening representation, and the current BUD activation boundary. It does not yet flip the `BUD` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full budget-resolver discharge artifact only after the checker, proof artifact, negative tests, envelope-DP audit, routing audit, strong-sidecar audit, and release-boundary transition are all represented.
