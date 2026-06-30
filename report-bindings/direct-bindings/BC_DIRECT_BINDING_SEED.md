# BC direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-BC-BRANCH-CYCLE-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/BC_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-branch-cycle0.mjs --json
```

This seed binds the historical Section 22 `BC` theorem-ledger row to the current branch-cycle finite transition category, cycle audit, branch audit, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
bcDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalBCTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers finite transition category representation, cycle-audit representation, branch-audit representation, checker-hardening representation, and the current BC activation boundary. It does not yet flip the `BC` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full branch-cycle discharge artifact only after the checker, proof artifact, negative tests, cycle/branch audits, and release-boundary transition are all represented.
