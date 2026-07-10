# Lean explicit-list residual routes

`lean/PNP/ResidualRoutes.lean` formalizes sound local route outcomes without claiming that the
report's route universe has been enumerated or exhausted.

## Executable scan

`strictEquivalentGainBool` combines exact finite truth-table equivalence with a strict gate-count
comparison. `firstListedGain` returns the first matching implementation in an explicit
caller-supplied list. Its soundness theorem proves that the result belongs to that list, is
semantically equivalent to the current implementation, and has fewer gates.

Because equivalent implementations have the same exhaustive reference minimum, every such gain
strictly decreases `residualSlack`. This is a mathematical descent theorem; it is not a claim that
the truth-table test or list scan runs in polynomial time.

## Proof-bearing outcomes

`ExactMinimumResult` contains an equivalent implementation and a proof that it is semantically
minimum. `ZeroSlackResult` contains a proof that the current implementation is semantically
minimum. Their soundness theorems derive the exhaustive reference-minimum equality and zero
residual slack.

The executable `GainScanOutcome` has only two constructors: `gain` and `unresolved`. It cannot
construct `exact` or `zeroSlack`. A wider `ResidualRouteResult` exposes those terminal constructors
only with their proof-bearing payloads.

## Fail-closed boundary

An `UnresolvedResult` records only that `firstListedGain` returned `none`. The corresponding theorem
rules out a gain among members of that one list and says nothing about unlisted implementations.
The module includes a redundant one-gate identity implementation with exhaustive minimum zero and
residual slack one. Scanning the empty list remains unresolved on that positive-slack example.

Consequently this layer does not prove candidate-list completeness, global absence of gains,
ZeroSlack, the BCEL/HN/BUD/selector contradiction, PCCMin loop exactness, residual-band
minimization, or polynomial runtime.

## Verification

```sh
node --test audits/lean-residual-routes0.test.mjs
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualRoutesAxiomAudit.lean
```

The axiom transcript covers all 30 explicit declarations exactly once.
