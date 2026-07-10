# Uniform residual-band exact minimizer

> **Historical assertion-checker record:** This UFS coordinate is superseded. A concrete exact
> residual-band minimizer and its polynomial bounds remain current formal obligations. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-RESIDUAL-BAND-MINIMIZER-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-004-ResidualBandMinimizerUniformPolynomial
```

Historical replay command:

```bash
npm run proof:uniform-residual-band-minimizer -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-uniform-residual-band-minimizer0.mjs --json --historical-replay
```

## Purpose

This surface recorded the fourth historical UFS assertion: that one uniform polynomial residual-band
exact minimizer handled every asserted locked-NAND instance.

The recorded assertion shape was:

```text
Lambda(W_phi) <= 4
PCCMin(W_phi) returns an exact minimum equivalent NAND word
phi in SAT iff |PCCMin(W_phi)| > B_phi
```

## Required proof obligations

```text
RBM-001-ResidualSlackBoundAllLockedInputs
RBM-002-StrictGainLowersSlack
RBM-003-ZeroSlackReturnsExactMinimum
RBM-004-ExactRouteReturnsExactMinimum
RBM-005-PolynomialIterationAndCertificateBounds
RBM-006-ThresholdDecisionUsesExactMinimum
RBM-007-NoHiddenOracleOrExactMinimizer
```

## What the historical checker accepted

The checker accepted records binding the UFS-003 threshold surface to deterministic, uniform,
totality, and polynomial-bound assertions. It did not formally prove those assertions.

## What this does not prove

This checker does not by itself prove the final SAT-in-P conclusion or activate theorem emission. Later checkers still need to bind the ZeroSlack closure into the full final soundness transition, the complexity implication, and the release transition.

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
