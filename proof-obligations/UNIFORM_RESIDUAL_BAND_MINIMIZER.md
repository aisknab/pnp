# Uniform residual-band exact minimizer

Coordinate:

```text
PNP-UNIFORM-RESIDUAL-BAND-MINIMIZER-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-004-ResidualBandMinimizerUniformPolynomial
```

Checker:

```bash
npm run proof:uniform-residual-band-minimizer
```

Direct checker command:

```bash
node pcc-uniform-residual-band-minimizer0.mjs --json
```

## Purpose

This surface discharges the fourth uniform-final-soundness sub-obligation: every locked NAND instance produced and threshold-certified by UFS-001 through UFS-003 is handled by one uniform polynomial residual-band exact minimizer.

The accepted theorem shape is:

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

## What this proves

The checker binds the UFS-003 threshold surface to the residual-band minimizer theorem: the minimizer is deterministic, uniform across input sizes, total on threshold-certified locked NAND instances, and polynomially bounded because the locked instances have residual slack at most four.

## What this does not prove

This checker does not by itself prove the final SAT-in-P conclusion or activate theorem emission. Later checkers still need to bind the ZeroSlack closure into the full final soundness transition, the complexity implication, and the release transition.

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
