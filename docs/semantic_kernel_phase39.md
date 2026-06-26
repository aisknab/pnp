# Semantic kernel hardening — phase 39

Phase 39 refines the remaining global final coordinate:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

The new semantic checker is:

```text
CheckGlobalFinalComplexitySemantic0
```

It preserves the phase-38 predecessor, reruns `CheckFinal0`, checks exact `PCCPack` surface alignment, and binds the final complexity coordinate to:

```text
global node digest
SAT-in-P dependency node digest
final theorem digest
SAT-in-P source implication digest
complexity source implication digest
final public theorem digest
positive CheckFinal0 record digest
negative probe digests
checker contract digest
binding digest
```

The checked source implication must retain the guarded complexity bridge metadata:

```text
id = PackageAcceptanceImpliesPEqualsNP
assumptions include SAT in P
assumptions include SAT is NP-complete
public = true
conditionalOnPackageAcceptance = true
usesSATinP = true
noUnconditionalClaim = true
```

Two fail-closed probes are required:

1. removing the `SAT in P` premise must make `CheckFinal0` reject;
2. clearing the no-unconditional-claim boundary must make `CheckFinal0` reject.

The new successor is:

```text
GlobalProofDAGSemanticFinalComplexitySuccessor0
```

After this layer the bounded semantic DAG coverage reports:

```text
GlobalDAG.FinalComplexityImplication = ready
GlobalDAG.FinalDerivations = ready
GlobalDAG.SemanticNodeDerivations = ready
```

Public emission remains deliberately separate:

```text
Release.PublicTheoremEmission = blocked
activeFinalNodeIds = []
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

The next layer should represent the public-emission and documentation-coordinate gate explicitly, rather than overwriting any sealed release artefact.
