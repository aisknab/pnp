# Uniform input family

Coordinate:

```text
PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01
```

Uniform final soundness obligation:

```text
UFS-001-InputFamilyUniformity
```

Checker:

```bash
npm run proof:uniform-input-family
```

Direct checker command:

```bash
node pcc-uniform-input-family0.mjs --json
```

## Purpose

This surface discharges the first uniform-final-soundness sub-obligation: the input family is not a bounded list of examples or row seeds. It is a single decidable schema covering every finite single-output NAND circuit.

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

## What this proves

The checker proves, by structural validation, that membership in the theorem input family is uniform and polynomial-time decidable for all finite sizes.

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
