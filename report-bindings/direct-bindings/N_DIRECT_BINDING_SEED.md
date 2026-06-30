# N direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-N-NORMALIZATION-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/N_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-normalization0.mjs --json
```

This seed binds the historical Section 22 `N` theorem-ledger row to the current traceable-normalization, witness-transport, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
nDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalNTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers traceable normalization representation, witness-transport representation, checker-hardening representation, and the current normalization activation boundary. It does not yet flip the `N` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full normalization-discharge artifact only after the checker, proof artifact, negative tests, and release-boundary transition are all represented.
