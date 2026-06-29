# Finite-to-unbounded family audit

Current coordinate:

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

The current answer is not “closed.” The audit records the criteria that a future unrestricted final-soundness checker must satisfy and prevents bounded small-model evidence from being silently generalized to all input sizes.

## Required uniformity criteria

```text
Uniform.InputFamily
Uniform.Generator
Uniform.PolynomialBound
Uniform.SemanticPreservation
Uniform.NoFiniteExtrapolation
```

Each criterion is currently represented but not discharged as unrestricted final soundness.

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

A later PR can close this gap only by adding an accepted checker that represents a uniform polynomial certificate-family proof for all SAT input sizes and transitions the release ladder accordingly.
