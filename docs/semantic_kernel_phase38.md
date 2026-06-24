# Semantic kernel hardening — phase 38 (bounded final SAT-reduction refinement)

## Purpose

Phase 37 refined the first two final coordinates:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
```

while keeping public theorem emission disabled. Phase 38 refines the next final coordinate:

```text
Final.AcceptedPackageImpliesSATinP
```

The phase deliberately keeps the complexity-class implication blocked:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

Accepted records state:

```text
boundedExecutableSATReductionRefinementOnly = true
unrestrictedSATReductionSoundnessNotClaimed = true
satInPPublicConclusionNotActivated = true
publicTheoremEmissionAllowed = false
```

Thus this layer is a bounded executable refinement of the version-zero SAT-reduction surface. It does not yet activate a public `SAT in P` conclusion and does not establish `P = NP`.

## New checker

The new checker is:

```text
CheckGlobalFinalSATReductionSemantic0
```

It accepts only a `GlobalFinalSATReductionSemanticInput0` containing:

- the phase-37 final-prefix predecessor surfaces;
- the aligned `PCCPack`;
- a generated `GlobalFinalSATReductionSemanticSuite0`;
- the exact bounded fail-closed policy.

The checker reruns:

```text
CheckGlobalProofDAGFinalPrefixSuccessor0
CheckFinalIntegration0
```

The predecessor must remain development-only, with final-prefix refinements ready and the SAT-reduction coordinate still blocked.

## Exact final-node contract

The global final node must retain:

```text
id = Final.AcceptedPackageImpliesSATinP
nodeKind = final
label = Final.AcceptedPackageImpliesSATinP
premises = [
  Package.G.LockedNANDThreshold,
  Package.O.ZeroSlackOracle,
  Final.GeneratedPackageSufficiency
]
conclusion = {
  tag: FinalTheoremAccepted0,
  theorem: Final.AcceptedPackageImpliesSATinP
}
imports = []
payload = {}
mode = Full
route = null
rank = null
```

The node must carry a positive polynomial bound within the global bounds envelope.

## Dependency binding

The derivation requires accepted predecessor semantic bindings for:

```text
Package.G.LockedNANDThreshold
Package.O.ZeroSlackOracle
Final.GeneratedPackageSufficiency
```

Each dependency's global-node digest and semantic refinement digest is carried into the SAT-reduction derivation.

## Final integration replay

`CheckFinalIntegration0` is replayed over the aligned `PCCPack.FinalIntegration` surface. This in turn replays:

```text
CheckGPack0
CheckGlobalProofDAG0
CheckFinalFrameworkMatch0
CheckSATDecision0
CheckSATBounds0
```

The phase binds digests for:

```text
FinalIntegration
FinalMatch
SATDecision
SATBounds
GPack
PCCMinBridge
AcceptedPackageImpliesSATinP source implication
```

## Reduction-surface checks

The checker validates that the final theorem source record exposes the exact version-zero bridge:

```text
exactMinimizer = PCCMin
residualBandBound = 4
residualBandPolynomial = true
lockedNANDReduction = true
satReduction = true
usesExactMinimum = true
rejectsApproximateMinimum = true
decisionComparator = minSize>baseline
```

The source implication must retain:

```text
id = PackageAcceptanceImpliesSATinP
conclusion = SAT in P
polynomial = true
usesPCCMinBridge = true
usesSATDecision = true
usesAcceptedGPack = true
usesAcceptedGlobalProofDAG = true
usesGlobalGThreshold = true
usesGThresholdProofRef = true
usesFinalIntegrationGlobalGLinkage = true
```

The SAT decision record must bind deterministic satisfiability-preserving NAND conversion, the exact baseline/full-word relation, the exact `minSize>baseline` comparator, and coherent SAT/UNSAT cases.

The SAT bounds record must bind:

```text
Converter.polynomial = true
LockedBuilder.polynomial = true
LockedBuilder.residualSlackMax = 4
Minimizer.exact = true
Minimizer.residualSlackBound = 4
DecisionProcedure.polynomial = true
DecisionProcedure.comparator = minSize>baseline
Bounds.polynomial = true
Bounds.finite = true
Bounds.exponent = 42
```

## Negative probes

Two fail-closed probes are required:

1. Mutating the decision comparator from `minSize>baseline` to `minSize>=baseline` must make `CheckFinalIntegration0` reject.
2. Mutating `SATBounds.Minimizer.exact` from `true` to `false` must make `CheckFinalIntegration0` reject.

The resulting reject-record digests are stored in the derivation.

## Digest-bound suite

The generated suite contains one `GlobalFinalSATReductionSemanticBinding0` for the SAT-reduction coordinate. It binds:

```text
global node digest
dependency node digests
final integration digest
final framework match digest
SAT decision digest
SAT bounds digest
GPack digest
PCCMin bridge digest
SAT implication source digest
checker-contract digest
binding digest
```

Caller-supplied readiness or truth assertions are rejected.

## Successor global gate

The new successor is:

```text
GlobalProofDAGSemanticFinalSATReductionSuccessor0
```

It preserves the phase-37 predecessor and activates exactly one additional semantic final-node refinement:

```text
Final.AcceptedPackageImpliesSATinP
```

The node becomes semantically refined in the overlay but remains publicly quarantined:

```text
satInPConclusionRemainsPubliclyQuarantined = true
activeFinalNodeIds = []
```

The remaining blocked final node is:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

## Readiness after phase 38

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

The global result remains:

```text
status = development-only
activeFinalNodeIds = []
legacyFinalNodesQuarantined = true
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-global-final-sat-reduction-semantic0.test.mjs \
  test/pcc-global-proof-dag-final-sat-reduction-successor0.test.mjs
```

The tests cover:

- predecessor preservation;
- exact final-node contract;
- dependency semantic-binding requirements;
- final integration replay;
- baseline, comparator, residual-slack, and polynomial-bound binding;
- decision-comparator and exact-minimizer negative probes;
- stale binding rejection;
- caller readiness rejection;
- semantic overlay activation of the SAT-reduction node;
- continued public quarantine and blocked `P = NP` implication.

## Next step

After this phase, the only remaining final blocker is the complexity implication:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

The next layer should independently represent the complexity-class bridge from `SAT in P` to `P = NP`, including the exact NP-completeness dependency, the language-class inclusions used, the conditional-public-claim boundary, and negative probes that reject an unconditional or premise-free public theorem. Only after that layer is complete should public theorem emission be considered.
