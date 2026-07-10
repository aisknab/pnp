# Uniform locked NAND construction

> **Historical assertion-checker record:** This UFS coordinate is superseded. Its accepted records
> do not prove a uniform polynomial locked-NAND construction. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01
```

Uniform final soundness obligation:

```text
UFS-002-LockedNANDConstructionUniformPolynomial
```

Historical replay command:

```bash
npm run proof:uniform-locked-nand-construction -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-uniform-locked-nand-construction0.mjs --json --historical-replay
```

## Purpose

This surface recorded the second historical UFS assertion: that one deterministic polynomial-time
builder generated a locked-NAND instance for every accepted `NANDCircuit0` record.

It depends on:

```text
UFS-001-InputFamilyUniformity
```

## Construction summary

For an input NAND circuit, the builder first normalizes the output convention so the represented output is a gate output. If the input output is already a gate, no gadget is added. If the output is an input or constant, a uniform constant/double-NAND gadget is appended.

The builder allocates these slot families:

```text
primary inputs X
trace slots T
source occurrence slots O
source locks R
trace locks L
final lock z
```

It then emits the macro inventory:

```text
Equality macro:              10 gates each
Constant-zero macro:          3 gates each
Constant-one macro:           2 gates each
NAND trace macro:            18 gates each
Prefix-conjunction node:      2 gates each
Final ternary conjunction:    4 gates total
```

The checked baseline formula is:

```text
baseline = 18*m + 10*wEq + 3*w0 + 2*w1 + 2*max(0, 3*m - 1)
fullWordSize = baseline + 4
residualSlackBound = 4
```

where `m` is the normalized gate count and `wEq`, `w0`, and `w1` count equality, constant-zero, and constant-one source-occurrence macros.

## What the historical checker accepted

The checker accepted fields stating that the construction was:

```text
total on the UFS-001 input family
deterministic
uniform across all input sizes
not a finite instance list
not bounded enumeration only
free of SAT/exact-minimization oracle calls
polynomial in encoded input size
```

## What this does not prove

This checker does not prove the locked NAND threshold theorem. That is the next obligation:

```text
UFS-003-ThresholdEquivalenceAllInputs
```

It also does not prove residual-band minimization, SAT in P, or P = NP.

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
