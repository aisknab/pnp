# HN direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-HN-HEREDITARY-NORMAL-FORMS-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/HN_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-hereditary-normal-forms0.mjs --json
```

This seed binds the historical Section 22 `HN` theorem-ledger row to the current hereditary shape recognition, BWL exactness, LN confluence, ParseOrExit completeness, leaf-tightness, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
hnDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalHNTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers hereditary-shape representation, BWL exactness representation, LN confluence representation, ParseOrExit representation, leaf-tightness representation, checker-hardening representation, and the current HN activation boundary. It does not yet flip the `HN` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full hereditary-normal-forms discharge artifact only after the checker, proof artifact, negative tests, HNShape/BWL/LN/ParseOrExit/leaf-tightness audits, and release-boundary transition are all represented.
