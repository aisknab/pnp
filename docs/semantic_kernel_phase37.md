# Semantic kernel hardening — phase 37 (bounded final-prefix refinement)

## Purpose

Phase 36 activated every required global package coordinate while keeping all final theorem nodes quarantined. The remaining global blocker was:

```text
GlobalDAG.FinalDerivations
```

Phase 37 splits that surface rather than activating all four final nodes at once. It introduces bounded executable refinements for:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
```

The downstream implication nodes remain blocked:

```text
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

Accepted records state explicitly:

```text
boundedExecutableFinalPrefixRefinementsOnly = true
unrestrictedFinalPrefixTheoremSoundnessNotClaimed = true
packAcceptanceDoesNotActivatePublicConclusion = true
```

This phase does not establish SAT in P or P = NP. The sealed `7072f8d` source/checker and artefact releases are not modified.

## Semantic final-prefix checker

The new checker is:

```text
CheckGlobalFinalPrefixSemantic0
```

It accepts only a `GlobalFinalPrefixSemanticInput0` containing:

- a development-purpose reflection KBundle;
- the legacy global proof DAG;
- the accepted infrastructure semantic suite;
- the accepted row pack and locked-NAND row family;
- the accepted row semantic suite;
- the complete local-package inventory;
- the accepted package semantic suite;
- an aligned version-zero `PCCPack0`;
- a generated `GlobalFinalPrefixSemanticSuite0`;
- the exact bounded scope and fail-closed policy.

## Package predecessor boundary

Before evaluating either prefix refinement, the checker reruns:

```text
CheckGlobalProofDAGPackageSuccessor0
```

The predecessor must remain development-only and expose:

```text
semanticKBundleFinalReady = true
globalInfrastructureSemanticReady = true
globalRowDerivationsReady = true
globalPackageDerivationsReady = true
globalFinalDerivationsReady = false
activeFinalNodeIds = []
publicTheoremEmissionAllowed = false
```

Its blocked final-node set must be exactly the complete four-node final set.

## Pack-sufficiency replay

The checker independently runs:

```text
CheckPackSufficiency0(PCCPack)
```

The result must accept as `PackSufficiency0NF`. The supplied pack must align exactly with the semantic predecessor surfaces:

```text
PCCPack.GlobalProofDAG = LegacyGlobalProofDAG
PCCPack.RowPack = RowPack
PCCPack.LocalPackages = LocalPackages
PCCPack.RowFamG = RowFamG
PCCPack.GPack = RowFamG.GPack
PCCPack.FinalIntegration.GlobalProofDAG = LegacyGlobalProofDAG
PCCPack.FinalIntegration.GPack = RowFamG.GPack
PCCPack.FinalTheorem.FinalIntegration = PCCPack.FinalIntegration
PCCPack.RowFamFinal.FinalTheorem = PCCPack.FinalTheorem
```

A separately accepted pack over a different global DAG cannot supply readiness to the active semantic predecessor.

## Digest-bound prefix suite

The generated suite is:

```text
GlobalFinalPrefixSemanticSuite0
```

It contains one `GlobalFinalPrefixSemanticBinding0` per prefix coordinate. Every binding includes:

```text
index
nodeId
globalNodeDigest
dependencyNodeId
dependencyNodeDigest
sourceRecordDigest
packCoreDigest
packManifestDigest
packTheoremDigest
canonicalBytesDigest
checkerContractDigest
bindingDigest
```

All values are recomputed from the live global nodes and the aligned pack. Caller-added readiness or theorem-truth assertions are rejected.

## Final.PackageSoundness refinement

The global node must retain exactly:

```text
nodeKind = final
id = Final.PackageSoundness
label = Final.PackageSoundness
premises = [Package.PACK.PackageSufficiency]
imports = []
mode = Full
payload = {}
route = null
rank = null
conclusion = {
  tag: FinalTheoremAccepted0,
  theorem: Final.PackageSoundness
}
```

Its package dependency must be the checked semantic refinement of:

```text
Package.PACK.PackageSufficiency
```

The source record is:

```text
PCCPack.PackSufficiencyTheorem.packageSufficiency
```

The checker requires the exact version-zero fields and runs a negative probe with:

```text
acceptedPackageValid = false
```

`CheckPackSufficiency0` must reject at:

```text
Coord = CheckPackSufficiency0.PackSufficiencyTheorem
Path = [
  PackSufficiencyTheorem,
  packageSufficiency,
  acceptedPackageValid
]
```

This establishes a fail-closed executable boundary for the represented pack contract. It is not an unrestricted mathematical package-soundness theorem.

## Final.GeneratedPackageSufficiency refinement

The global node must retain exactly:

```text
nodeKind = final
id = Final.GeneratedPackageSufficiency
label = Final.GeneratedPackageSufficiency
premises = [Final.PackageSoundness]
imports = []
mode = Full
payload = {}
route = null
rank = null
conclusion = {
  tag: FinalTheoremAccepted0,
  theorem: Final.GeneratedPackageSufficiency
}
```

The refinement requires the checked `Final.PackageSoundness` prefix refinement. Its source record is:

```text
PCCPack.PackSufficiencyTheorem.generatedPackageSufficiency
```

The generated core must retain the version-zero boundary:

```text
kind = PCCCorePackage0
generatedBy = GeneratePCCPack
generatorUntrusted = true
materializedOutputOnly = true
canonicalByteEquality = true
noDigestOnlyEquality = true
excludesAcceptRun = true
includesAcceptRun = false
```

The checker runs a negative probe with:

```text
canonicalByteEquality = false
```

and requires `CheckPackSufficiency0` to reject at the exact generated-package theorem path.

## Positive and negative record binding

Each accepted prefix refinement records:

```text
global node digest
dependency-node digest
dependency-refinement digest
source-record digest
pack core, manifest, and theorem digests
checker-contract digest
positive CheckPackSufficiency0 record digest
negative CheckPackSufficiency0 record digest
refinement-conclusion digest
refinement digest
```

This prevents a structural final node, a stale pack, or a caller assertion from inheriting readiness from a different executable check.

## Successor global gate

The new successor is:

```text
GlobalProofDAGSemanticFinalPrefixSuccessor0
```

It reruns the phase-36 package predecessor, runs `CheckGlobalFinalPrefixSemantic0`, and rebuilds the semantic overlay.

The two prefix nodes enter the semantic-node set:

```text
semanticFinalPrefixNodeIds = [
  Final.PackageSoundness,
  Final.GeneratedPackageSufficiency
]
globalFinalPrefixRefinementsReady = true
```

The remaining blocked final-node set becomes:

```text
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

Semantic refinement does not make either prefix node publicly active. All four final nodes remain in the quarantine set and `activeFinalNodeIds` remains empty.

## Readiness decomposition

Ready scoped surfaces:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.InfrastructureDerivations
GlobalDAG.RowDerivations
GlobalDAG.PackageDerivations
GlobalDAG.FinalPrefixRefinements
```

Remaining blockers:

```text
GlobalDAG.FinalSATReductionDerivation
GlobalDAG.FinalComplexityImplication
```

The first remaining blocker must represent the accepted-package-to-SAT-in-P reduction, including exact-minimizer soundness, locked-NAND encoding correctness, decision extraction, and polynomial runtime. The second must remain downstream of that result and represent the complexity-class implication explicitly.

## Public quarantine

Development results remain:

```text
status = development-only
activeFinalNodeIds = []
quarantinedFinalNodeIds = [all four final nodes]
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

A final-purpose successor record rejects while either remaining implication gate is blocked.

## Verification targets

Durable CI runs:

```bash
node --test test/pcc-global-final-prefix-semantic0.test.mjs
node --test test/pcc-global-proof-dag-final-prefix-successor0.test.mjs
```

The dedicated workflow also reruns the frozen public release-surface tests. The tests cover:

- exact two-node prefix coverage;
- package-predecessor preservation;
- exact global node contracts;
- exact pack-surface alignment;
- positive pack-sufficiency replay;
- negative package-validity and canonical-byte probes;
- stale binding and caller-readiness rejection;
- digest binding through the semantic overlay;
- continued quarantine of every final node;
- explicit SAT-reduction and complexity-implication blockers;
- preservation of the frozen public API and release surface.

## Next step

The next phase should address only:

```text
Final.AcceptedPackageImpliesSATinP
```

It must not infer SAT in P merely from pack acceptance fields. It should introduce an independently checked reduction object that binds the SAT formula encoding, locked-NAND construction, threshold decision rule, exact-minimizer interface, completeness and soundness directions, and polynomial runtime ledger. `Final.AcceptedPackageImpliesPEqualsNP` must remain quarantined until that reduction node is ready.
