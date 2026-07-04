# Uniform final soundness theorem target

Coordinate:

```text
PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01
```

Machine-readable manifest:

```text
proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json
```

Checker:

```bash
npm run proof:uniform-final-soundness-target
```

Direct checker command:

```bash
node pcc-uniform-final-soundness-target0.mjs --json
```

## Purpose

This is the first proof-work surface for replacing the current finite-to-unbounded audit with a code-bound all-input-size theorem.

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

The current code already represents these as known gaps. This target converts them into a concrete list of uniform proof obligations that future checkers can discharge.

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

The repository is actively developing the proof checker stack. `package.json` may add narrowly scoped proof-development scripts under the `proof:*` namespace. Such scripts must directly invoke a checker as:

```text
node pcc-<checker-name>0.mjs --json
```

This keeps proof work accessible without opening arbitrary package-script drift.

## Release discipline

This target deliberately separates mathematical proof from external review.

External review can report independent runs, bugs, or confirmations, but it is not a premise of the theorem. The theorem must be discharged by code-bound uniform obligations.

Current boundary:

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

This file does not prove P = NP. It defines the machine-checkable theorem target that must be accepted before the verifier can honestly emit the final theorem.
