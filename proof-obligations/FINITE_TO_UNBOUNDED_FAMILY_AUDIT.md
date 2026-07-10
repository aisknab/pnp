# Finite-to-unbounded family audit

> **Superseded audit:** This June 2026 audit is historical assertion-checker evidence. It did not
> close the finite-to-unbounded gap, and later UFS acceptance did not formally prove that closure.
> Current obligations are in
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01
```

Machine-readable manifest:

```text
proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json
```

Checker:

```bash
node pcc-finite-to-unbounded-family-audit0.mjs --json
```

This audit represents the activation-critical question:

```text
Does every finite certificate schema uniformly cover all SAT input sizes in polynomial time?
```

This historical audit recorded that the answer was not closed. Current reconstruction requires a
concrete all-size formal theorem and complexity model rather than a later assertion-checker transition.

## Required uniformity criteria

```text
Uniform.InputFamily
Uniform.Generator
Uniform.PolynomialBound
Uniform.SemanticPreservation
Uniform.NoFiniteExtrapolation
```

Each criterion was represented but not formally discharged.

## Boundary

The audit is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

This gap can be closed only by the concrete formal derivations required by the current status. An
accepted JavaScript record or release-ladder transition is insufficient.
