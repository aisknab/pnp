# Uniform final soundness theorem target

> **Historical target, not a proof:** This UFS manifest and checker are retained as superseded
> assertion-checker evidence. They do not discharge the current formal obligations. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01
```

Machine-readable manifest:

```text
proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json
```

Historical replay command:

```bash
npm run proof:uniform-final-soundness-target -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-uniform-final-soundness-target0.mjs --json --historical-replay
```

## Purpose

This was the first historical checker surface intended to replace a finite-to-unbounded audit with an
all-input-size theorem target. It defined a target but did not prove it.

The target theorem is:

```text
For every Boolean/NAND SAT input family instance phi, the repository provides a uniform polynomial-time construction and checker-accepted proof path such that locked NAND thresholding plus residual-band minimization decides SAT in polynomial time; therefore SAT is in P and P equals NP.
```

The important words are:

```text
for every input size
uniformly
polynomial time
checker accepted
```

Bounded small models, row-surface coverage, direct-binding seeds, or historical report prose do not discharge this target by themselves.

## Current blockers tied to this target

```text
GAP-001-UnrestrictedFinalSoundness
GAP-003-BoundedSmallModelsNotUniformProof
GAP-004-FiniteToUnboundedUniformity
GAP-005-NoHiddenOracleSemanticCompleteness
```

The historical code represented these as known gaps and then as UFS assertion records. Current
reconstruction requires concrete formal derivations rather than accepted assertion fields.

## Required uniform obligations

```text
UFS-001-InputFamilyUniformity
UFS-002-LockedNANDConstructionUniformPolynomial
UFS-003-ThresholdEquivalenceAllInputs
UFS-004-ResidualBandMinimizerUniformPolynomial
UFS-005-ZeroSlackContradictionUniform
UFS-006-NoHiddenOracleSemanticCompleteness
UFS-007-ComplexityConclusionUniform
UFS-008-ReleaseTransitionFromProofOnly
```

Each obligation is required for a real unrestricted final-soundness discharge. The target checker rejects any attempt to flip this manifest into theorem activation.

## Proof-development script namespace

The historical package retained narrowly scoped `proof:*` replay scripts. On current `main`, each
requires explicit historical replay:

```text
node pcc-<checker-name>0.mjs --json --historical-replay
```

This keeps proof work accessible without opening arbitrary package-script drift.

## Release discipline

This target deliberately separates mathematical proof from external review.

External review can report independent runs, bugs, or confirmations, but it is not a premise of the theorem. The theorem must be discharged by code-bound uniform obligations.

Historical boundary recorded by this target:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The proof-track aim is to clear `Release.UnrestrictedFinalSoundness` by code. The public/reputation track can continue to record external review separately.

## What this file does not claim

This file does not prove `P = NP`. Acceptance of its historical checker is not a future activation
condition. The only acceptable future gate is the concrete Lean gate in the formal-reconstruction
notice.
