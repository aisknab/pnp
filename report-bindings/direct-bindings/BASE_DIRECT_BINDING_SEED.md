# Base direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-BASE-SEMANTICS-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-base-semantics0.mjs --json
```

This seed binds the historical Section 22 `Base` theorem-ledger row to the current executable NAND direct-wire semantics stack, report theorem inventory, coverage matrix, closure plan, and proof-obligation ledger.

## Current scope

```text
baseDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalBaseTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers direct-wire NAND syntax, open-function evaluation, compatible replacement semantics, and the current slack-law ledger surface. It does not yet flip the `Base` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add the missing full theorem-discharge artifact and only then update the coverage matrix and closure plan through a checked transition.
