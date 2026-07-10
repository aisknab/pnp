# Uniform locked NAND threshold theorem

> **Historical assertion-checker record:** This UFS coordinate is superseded. The threshold theorem
> remains a current formal obligation and is not proved by acceptance of this checker. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01
```

Uniform final soundness obligation:

```text
UFS-003-ThresholdEquivalenceAllInputs
```

Historical replay command:

```bash
npm run proof:uniform-locked-nand-threshold -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-uniform-locked-nand-threshold0.mjs --json --historical-replay
```

## Purpose

This surface recorded the third historical UFS assertion: that the UFS-002 construction satisfied the
SAT threshold relation for every record in the asserted UFS-001 family. It did not formally derive
that all-input theorem.

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

The historical record kept this boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
