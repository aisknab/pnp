# Semantic kernel hardening — phase 39 (guarded final complexity refinement)

## Purpose

Phase 38 added a bounded semantic refinement for:

```text
Final.AcceptedPackageImpliesSATinP
```

while keeping the final complexity coordinate blocked. Phase 39 represents the standard guarded bridge:

```text
SAT in P
SAT is NP-complete
P subseteq NP
----------------
P = NP
```

at the remaining global coordinate:

```text
Final.AcceptedPackageImpliesPEqualsNP
```

This phase does **not** activate public theorem emission. It distinguishes complete bounded final-coordinate coverage from unrestricted mathematical soundness.

Accepted records state:

```text
guardedComplexityRefinementOnly = true
cookLevinFormalizationIncluded = false
standardTheoremDependencyTrustRequired = true
unrestrictedComplexityImplicationSoundnessNotClaimed = true
unrestrictedSATReductionSoundnessNotClaimed = true
publicTheoremEmissionAllowed = false
```

## Standalone complexity bridge

The new standalone checker is:

```text
CheckComplexityBridge0
```

It accepts only a `ComplexityBridgeInput0` with:

- a digest-bound `SAT in P` predecessor source;
- the exact version-zero standard complexity basis;
- the exact guarded conditional equality claim;
- the fail-closed scope and policy.

The standard basis records:

```text
P  = deterministic polynomial-time decision
NP = nondeterministic polynomial-time decision
P subseteq NP
SAT is NP-complete under deterministic polynomial-time many-one reductions
L <=p A and A in P implies L in P
mutual inclusion implies class equality
```

The SAT NP-completeness entry identifies `CookLevin` as a trusted standard mathematical dependency and explicitly records:

```text
formalProofIncluded = false
```

The checker therefore derives only a guarded conditional conclusion. It does not turn the dependency metadata into a self-contained Cook–Levin formalization.

## Logical derivation recorded by the bridge

The accepted bridge contains the following dependency DAG:

```text
Complexity.SATInP
Complexity.SATNPComplete
  -> Complexity.NPSubsetP
Complexity.PSubsetNP
  -> Complexity.ConditionalPEqualsNP
```

The terminal record states:

```text
conditionalOnPackageAcceptance = true
noUnconditionalClaim = true
publiclyActive = false
```

## Global final-complexity checker

The new global checker is:

```text
CheckGlobalFinalComplexitySemantic0
```

It reruns:

```text
CheckGlobalProofDAGFinalSATReductionSuccessor0
CheckFinal0
CheckComplexityBridge0
```

The phase-38 predecessor must remain development-only and must expose:

```text
globalFinalSATReductionDerivationReady = true
globalFinalComplexityImplicationReady = false
activeFinalNodeIds = []
blockedFinalNodeIds = [Final.AcceptedPackageImpliesPEqualsNP]
```

The `PCCPack` surfaces must align exactly with the semantic predecessor inputs.

## Exact global-node contract

The final complexity node must retain:

```text
id = Final.AcceptedPackageImpliesPEqualsNP
nodeKind = final
label = Final.AcceptedPackageImpliesPEqualsNP
premises = [Final.AcceptedPackageImpliesSATinP]
conclusion = {
  tag: FinalTheoremAccepted0,
  theorem: Final.AcceptedPackageImpliesPEqualsNP
}
imports = []
payload = {}
mode = Full
route = null
rank = null
```

The node must carry a positive polynomial bound within the global bounds envelope.

## Source implication and conditional-public boundary

The final theorem source implication must be exactly:

```text
id = PackageAcceptanceImpliesPEqualsNP
assumptions = [SAT in P, SAT is NP-complete]
conclusion = P = NP
conditionalOnPackageAcceptance = true
usesSATinP = true
noUnconditionalClaim = true
```

The public theorem record must preserve:

```text
antecedent = CheckPCCPackexp(GeneratePCCPack())=accept
consequent = P = NP
noClaimBeforeAccept = true
finalVerdict = conditional
```

These records are checked as source metadata. They remain publicly inactive in the phase-39 semantic overlay.

## Negative probes

Two fail-closed probes are required:

1. Removing the `SAT in P` premise from the guarded complexity claim must make `CheckComplexityBridge0` reject at the claim-assumption coordinate.
2. Setting `noUnconditionalClaim` to false must make `CheckComplexityBridge0` reject at the guarded claim coordinate.

Both reject-record digests are included in the final complexity derivation.

## Digest bindings

The generated semantic suite binds:

```text
global complexity node digest
SAT-reduction predecessor node digest
SAT-reduction semantic binding digest
standard complexity basis digest
source implication digest
conditional public theorem digest
checker-contract digest
binding digest
```

The accepted derivation additionally binds:

```text
phase-38 SAT-reduction derivation digest
CheckFinal0 accept-record digest
CheckComplexityBridge0 accept-record digest
premise-removal reject-record digest
unconditional-claim reject-record digest
conclusion digest
```

Caller-supplied truth or readiness fields are rejected.

## Successor global gate

The new successor is:

```text
GlobalProofDAGSemanticFinalComplexitySuccessor0
```

It adds the final complexity node to the bounded semantic overlay. After the overlay update:

```text
blockedFinalNodeIds = []
allGlobalFinalCoordinatesBoundedRefined = true
```

This does not mean the final theorem is publication-ready. Every final node remains quarantined:

```text
activeFinalNodeIds = []
quarantinedFinalNodeIds = all four final coordinates
```

The computed gate introduces the explicit remaining blocker:

```text
GlobalDAG.UnrestrictedFinalSoundness
```

The blocker records that bounded executable refinements do not establish unrestricted SAT-reduction soundness and that the checker stack does not contain a formal Cook–Levin proof.

## Readiness after phase 39

Ready bounded surfaces:

```text
GlobalDAG.InfrastructureDerivations
GlobalDAG.RowDerivations
GlobalDAG.PackageDerivations
GlobalDAG.FinalPrefixRefinements
GlobalDAG.FinalSATReductionDerivation
GlobalDAG.FinalComplexityImplication
GlobalDAG.BoundedFinalSemanticCoverage
```

Still blocked:

```text
GlobalDAG.UnrestrictedFinalSoundness
```

The global result remains:

```text
status = development-only
globalFinalDerivationsReady = false
globalSemanticNodeDerivationsReady = false
unrestrictedFinalSoundnessReady = false
activeFinalNodeIds = []
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

## Verification targets

Durable CI runs:

```bash
node --test test/pcc-complexity-bridge0.test.mjs
node --test test/pcc-global-final-complexity-semantic0.test.mjs
node --test test/pcc-global-proof-dag-final-complexity-successor0.test.mjs
```

The tests cover:

- exact standard complexity basis;
- guarded mutual-inclusion derivation;
- rejection of missing premises and unconditional claims;
- phase-38 predecessor preservation;
- exact final complexity node contract;
- SAT-reduction semantic dependency binding;
- source implication and conditional-public boundary;
- stale binding rejection;
- complete bounded final-coordinate coverage;
- continued quarantine and publication denial.

## Next proof obligation

Phase 39 completes the bounded semantic coordinate migration. It does not close the mathematical proof gap. The remaining work is to replace bounded metadata refinement with independently checkable unrestricted soundness for the SAT-reduction/minimizer route and, if a self-contained foundation is required, a formal NP-completeness dependency. Only a successor that closes those obligations should be permitted to set:

```text
unrestrictedFinalSoundnessReady = true
finalTheoremReady = true
publicTheoremEmissionAllowed = true
```
