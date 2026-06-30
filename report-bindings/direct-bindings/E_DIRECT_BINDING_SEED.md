# E direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-E-VERIFYDW-SOUNDNESS-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/E_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-verifydw-soundness0.mjs --json
```

This seed binds the historical Section 22 `E` theorem-ledger row to the current VerifyDW soundness, obligation-flattening, no-hidden-oracle, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
eDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalETheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers the VerifyDW soundness surface, obligation-flattening surface, current executable no-hidden-oracle boundary, and the represented semantic-completeness gap for hidden-oracle absence. It does not yet flip the `E` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full VerifyDW discharge artifact only after the checker, proof artifact, negative tests, and gap-status transition are all represented.
