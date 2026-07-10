# Uniform complexity conclusion

> **Historical assertion-checker record:** This UFS coordinate is superseded and does not establish
> a uniform SAT algorithm, `SAT in P`, or `P = NP`. Current authority is
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json); see
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-COMPLEXITY-CONCLUSION-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-007-ComplexityConclusionUniform
```

Historical replay command:

```bash
npm run proof:uniform-complexity-conclusion -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-uniform-complexity-conclusion0.mjs --json --historical-replay
```

## Purpose

This surface recorded the seventh historical UFS assertion. It checked fields claiming that the
locked-NAND procedure was a polynomial SAT decision procedure and that the standard implication
`SAT in P => P = NP` was bound. It did not derive those claims formally.

The recorded assertion shape was:

```text
for every input phi:
  construct W_phi and B_phi uniformly in polynomial time
  compute exact minimum |PCCMin(W_phi)| uniformly in polynomial time
  decide SAT by |PCCMin(W_phi)| > B_phi
therefore SAT in P
since SAT is NP-complete, P = NP
```

## Required proof obligations

```text
CC-001-SATNPCompleteBound
CC-002-UniformLockedReductionPolynomial
CC-003-ThresholdEquivalenceAllInputs
CC-004-ExactMinimizerPolynomial
CC-005-NoHiddenOracleDiscipline
CC-006-SATDecisionPolynomial
CC-007-SATInPImpliesPEqualsNP
CC-008-ReleaseGateStillSeparate
```

## What the historical checker accepted

The checker accepted records stating that UFS-001 through UFS-006 composed into a polynomial SAT
decision procedure. Acceptance verified implemented predicates over assertion-bearing records, not
the mathematical truth of that composition.

## What this does not prove

This checker does not clear `Release.UnrestrictedFinalSoundness` and does not activate public theorem emission. The next required obligation is:

```text
UFS-008-ReleaseTransitionFromProofOnly
```

The historical record kept this intermediate boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
