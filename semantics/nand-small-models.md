# NAND direct-wire small-model audit

This directory records the current small-model audit coordinate:

```text
PNP-NAND-SMALL-MODELS-2026-06-27-01
```

The machine-readable configuration is:

```text
semantics/nand-small-models-config.json
```

The bounded enumerator is:

```text
semantics/nand-small-models.mjs
```

Run the audit with:

```bash
npm run semantics:nand:small-models
```

## Configured universe

The current seed audit exhaustively enumerates one-output NAND direct-wire words with:

```text
boundarySizes = [0, 1, 2]
maxGates = 2
outputArity = 1
includeConstants = true
gateInputSymmetry = unordered-NAND-input-pairs
```

For every generated word, the audit validates the word shape, evaluates the truth table, checks that size is the NAND gate count, groups by truth-table class, and computes the brute-force minimum size of each class inside the configured universe.

## Replacement checks

For each boundary size, equivalent same-boundary words are checked through `compatibleReplacement0`. The audit also chooses a non-equivalent same-boundary pair and requires replacement compatibility to reject.

## Scope

This is a bounded small-model seed, not full semantic coverage for every locked-NAND theorem:

```text
smallModelsReady = true
fullSmallModelCoverageProved = false
```

Future PRs should raise the configured bounds, add multi-output exhaustive slices, and connect the small-model universe to locked-NAND SAT-threshold tests.

## Boundary

The audit is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
