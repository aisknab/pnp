# FT direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-FT-FINITE-TABLE-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/FT_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-finite-table0.mjs --json
```

This seed binds the historical Section 22 `FT` theorem-ledger row to the current finite-table coverage, explicit normalization transport, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
ftDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalFTTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers finite-table coverage representation, normalization-transport representation, checker-hardening representation, and the current FT activation boundary. It does not yet flip the `FT` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full finite-table discharge artifact only after the checker, proof artifact, negative tests, and release-boundary transition are all represented.
