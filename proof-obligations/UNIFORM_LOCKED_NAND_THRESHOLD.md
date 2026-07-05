# Uniform locked NAND threshold theorem

Coordinate:

```text
PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01
```

Uniform final soundness obligation:

```text
UFS-003-ThresholdEquivalenceAllInputs
```

Checker:

```bash
npm run proof:uniform-locked-nand-threshold
```

Direct checker command:

```bash
node pcc-uniform-locked-nand-threshold0.mjs --json
```

## Purpose

This surface discharges the third uniform-final-soundness sub-obligation: the locked NAND construction from UFS-002 satisfies the SAT threshold theorem for every input in the UFS-001 input family.

The target theorem shape is:

```text
phi notin SAT => mu(W_phi) = B_phi
phi in SAT    => B_phi + 1 <= mu(W_phi) <= B_phi + 4
phi in SAT iff mu(W_phi) > B_phi
Lambda(W_phi) <= 4
```

where

```text
B_phi = 18*m + 10*wEq + 3*w0 + 2*w1 + 2*max(0, 3*m - 1)
|W_phi| = B_phi + 4
```

## Required proof obligations

```text
THR-001-BaselineDistinctAllInputs
THR-002-TraceEquivalenceAllInputs
THR-003-ZeroOutputConventionAllInputs
THR-004-FinalLockSeparationAllInputs
THR-005-ThresholdEquivalenceAllInputs
THR-006-ResidualSlackBoundAllInputs
```

## What this does not prove

This checker does not prove residual-band minimization, SAT in P, or P = NP. The next required obligation is:

```text
UFS-004-ResidualBandMinimizerUniformPolynomial
```

Current boundary remains:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
