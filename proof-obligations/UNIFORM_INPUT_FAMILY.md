# Uniform input family

> **Historical assertion-checker record:** This UFS coordinate is superseded and does not prove an
> all-size input-family theorem. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01
```

Uniform final soundness obligation:

```text
UFS-001-InputFamilyUniformity
```

Historical replay command:

```bash
npm run proof:uniform-input-family -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-uniform-input-family0.mjs --json --historical-replay
```

## Purpose

This surface recorded the first historical UFS assertion: that an input schema covered every finite
single-output NAND circuit rather than a bounded example list.

The accepted input object is:

```text
NANDCircuit0 = {
  kind: "NANDCircuit0",
  version: 0,
  inputCount: nonnegative safe integer,
  gates: topologically ordered NAND gates,
  output: source reference
}
```

Each gate has operation `NAND` and two source references. Sources are:

```text
input(i)   where 0 <= i < inputCount
const(v)   where v in {0,1}
gate(j)    where j is an earlier gate
```

The output may reference an input, constant, or any existing gate.

## What the historical checker accepted

The checker structurally validated records asserting uniform, polynomial-time decidable membership.
It did not provide the current concrete complexity model or a formal all-size proof.

It accepts only if:

```text
allFiniteSizesCovered = true
schemaUniformAcrossSizes = true
finiteInstanceList = false
boundedEnumerationOnly = false
membershipTimeBound is polynomial
```

## What this does not prove

This does not prove the locked NAND construction, threshold equivalence, residual-band minimization, SAT in P, or P = NP. It discharges only the input-family quantifier needed before those later obligations can be checked.

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
