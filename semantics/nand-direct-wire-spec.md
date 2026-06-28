# NAND direct-wire executable semantics

This directory defines the current executable NAND direct-wire semantics coordinate:

```text
PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01
```

The machine-readable seed specification is:

```text
semantics/nand-direct-wire-spec.json
```

The reference evaluator is:

```text
semantics/nand-direct-wire-reference.mjs
```

Run the checker with:

```bash
npm run semantics:nand
```

## Scope

The seed specification covers:

```text
NAND gate syntax
open carrier boundary tuple
constant sources
direct-wire topological gate order
multi-output tuple semantics
truth-table evaluation
word size as NAND gate count
truth-table equivalence
compatible replacement semantics for same boundary and output arity
```

This is intentionally a seed executable semantics, not a full formalization of every historical locked-NAND construction theorem:

```text
semanticsReady = true
fullSemanticsCoverageProved = false
```

## Word shape

A direct-wire word has:

```text
kind = NANDDirectWireWord0
boundary = ordered unique boundary names
gates = ordered NAND gates
outputs = ordered source references
```

Sources may be boundary variables, constants, or earlier gate outputs. A gate may only reference earlier gates, never future gates. This enforces a topological direct-wire order.

## Evaluation

For each boundary assignment, gates are evaluated in order. A NAND gate computes:

```text
nand(a,b) = 1 iff not(a and b)
```

The output tuple is the ordered list of values obtained by evaluating each output source.

## Equivalence and replacement

Two words are equivalent when they have the same ordered boundary tuple, the same output arity, and identical output bit-vectors for every boundary assignment.

A replacement is compatible with a support word when it has the same boundary tuple and output arity and is truth-table equivalent. This seed checker treats compatibility at the open-word boundary level; richer carrier/profile compatibility remains represented by later checker families and trust-base tasks.

## Boundary

The semantics checker is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The historical report uses direct NAND semantics and locked NAND threshold claims. This executable seed is the new public-review path for making those semantics inspectable and testable before the final report/supersession pass.
