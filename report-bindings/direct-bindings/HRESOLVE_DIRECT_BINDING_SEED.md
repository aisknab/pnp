# HResolve direct-binding seed

Current coordinate:

```text
PNP-DIRECT-BIND-HRESOLVE-GLOBAL-HEREDITARY-RESOLVER-SEED-2026-06-27-01
```

Machine-readable manifest:

```text
report-bindings/direct-bindings/HRESOLVE_DIRECT_BINDING_SEED.json
```

Checker:

```bash
node pcc-direct-bind-hresolve0.mjs --json
```

This seed binds the historical Section 22 `HResolve` theorem-ledger row to the current global hereditary resolver, exact-minimum route, gain route, strong NoHereditary sidecar, H-disjoint family audit, checker-hardening, theorem inventory, coverage matrix, closure plan, proof-obligation ledger, and gap-ledger surfaces.

## Current scope

```text
hresolveDirectBindingSeedReady = true
directCheckerBindingComplete = false
fullHistoricalHResolveTheoremDischarged = false
publicTheoremEmissionAllowedByBinding = false
```

The seed covers global resolver representation, exact-minimum route representation, gain-route representation, strong NoHereditary sidecar representation, H-disjoint family representation, checker-hardening representation, and the current HResolve activation boundary. It does not yet flip the `HResolve` row in the coverage matrix to `directCheckerBindingComplete = true`.

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

The next direct-binding PR for this row should add a full global hereditary resolver discharge artifact only after the checker, proof artifact, negative tests, exact-minimum/gain/sidecar audits, H-disjointness audit, and release-boundary transition are all represented.
