# Semantic kernel hardening — phase 38 (bounded final decision refinement)

## Purpose

Phase 37 refined the first two final coordinates:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
```

Phase 38 refines the next final coordinate:

```text
Final.AcceptedPackageImpliesSATinP
```

The layer replays the executable final-integration, framework-match, decision, and polynomial-bound checkers, and digest-binds the global final node to those accepted executable records.

This phase deliberately does **not** activate the public final theorem and does **not** claim the downstream complexity-class implication. The remaining final coordinate stays blocked:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

## New checker

The new checker is:

```text
CheckGlobalFinalSATSemantic0
```

It requires the phase-37 predecessor:

```text
CheckGlobalProofDAGFinalPrefixSuccessor0 = accept
```

The predecessor must remain development-only, expose no active final node, and keep the SAT implication blocked before this phase.

## Executable final-integration replay

The checker replays:

```text
CheckFinalIntegration0
CheckFinalFrameworkMatch0
CheckSATDecision0
CheckSATBounds0
```

The accepted decision surface must retain:

```text
comparator = minSize>baseline
usesExactMinimum = true
rejectsApproximateMinimum = true
preservesSatisfiability = true
```

The accepted bounds surface must retain:

```text
residualSlackBound = 4
Bounds.finite = true
Bounds.polynomial = true
Bounds.exponent = 42
```

The pack surfaces must align exactly with the semantic predecessor inputs.

## Global final-node contract

`Final.AcceptedPackageImpliesSATinP` must retain:

```text
nodeKind = final
label = Final.AcceptedPackageImpliesSATinP
premises = [
  Package.G.LockedNANDThreshold,
  Package.O.ZeroSlackOracle,
  Final.GeneratedPackageSufficiency
]
imports = []
mode = Full
payload = {}
conclusion = {
  tag: FinalTheoremAccepted0,
  theorem: Final.AcceptedPackageImpliesSATinP
}
```

The checker verifies that the two package premises and the generated-package final-prefix premise are semantically active in the predecessor overlay.

## Digest-bound semantic suite

The generated suite is:

```text
GlobalFinalSATSemanticSuite0
```

It binds the global node, dependency nodes, final integration, framework, decision, bounds, GPack, pack core, pack manifest, checker contract, and aggregate binding digest.

## Negative probes

The checker requires two mutation probes to reject:

```text
SATDecision.DecisionRule.usesExactMinimum = false
SATBounds.Bounds.polynomial = false
```

The rejection digests are included in the final semantic refinement record.

## Successor global gate

The successor is:

```text
GlobalProofDAGSemanticFinalSATSuccessor0
```

It activates only the SAT implication node as a bounded semantic refinement:

```text
globalFinalSATReductionDerivationReady = true
```

It leaves the complexity implication blocked:

```text
globalFinalComplexityImplicationReady = false
globalFinalDerivationsReady = false
globalSemanticNodeDerivationsReady = false
```

The active final set remains empty:

```text
activeFinalNodeIds = []
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

## Current readiness after merge

Ready scoped surfaces:

```text
GlobalDAG.InfrastructureDerivations
GlobalDAG.RowDerivations
GlobalDAG.PackageDerivations
GlobalDAG.FinalPrefixRefinements
GlobalDAG.FinalSATReductionDerivation
```

Remaining blocker:

```text
GlobalDAG.FinalComplexityImplication
```

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-global-final-sat-semantic0.test.mjs \
  test/pcc-global-proof-dag-final-sat-successor0.test.mjs
```

## Next step

After this phase, the final remaining layer is the complexity implication:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

That phase should represent the NP-completeness bridge and the final complexity-class implication separately from the bounded decision refinement. Public theorem emission should remain disabled until that final coordinate is independently ready.
