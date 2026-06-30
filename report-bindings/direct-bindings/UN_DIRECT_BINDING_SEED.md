# UN direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-UN-UNARY-DECODER-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/UN_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-unary-decoder0.mjs --json
```

This seed binds the historical Section 22 `UN` theorem-ledger row to the current unary-decoder full-lift criterion, blocked intervals, clean spines, BCLeak token boundary, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
unDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalUNTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers unary full-lift criterion representation, blocked-interval representation, clean-spine extraction representation, BCLeak token-boundary representation, checker-hardening representation, and the current UN activation boundary. It does not yet flip the `UN` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full unary-decoder discharge artifact only after the checker, proof artifact, negative tests, blocked-interval audit, clean-spine audit, token-boundary audit, and release-boundary transition are all represented.
