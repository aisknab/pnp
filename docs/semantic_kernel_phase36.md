# Semantic kernel hardening — phase 36 (bounded executable package refinement)

## Purpose

Phase 35 activated all required global row coordinates and carried their accepted executable row records through the global semantic overlay. The remaining global blockers were:

```text
GlobalDAG.PackageDerivations
GlobalDAG.FinalDerivations
```

Phase 36 addresses the package surface by binding every required global package-theorem coordinate to:

- its exact global package node;
- the corresponding checked local package record;
- its accepted semantic row derivation;
- its local import dependencies;
- a canonical positive executable checker result;
- a canonical negative theorem-identity rejection result.

The accepted scope is deliberately bounded. Every accepted record states:

```text
boundedExecutablePackageRefinementsOnly = true
unrestrictedPackageTheoremSoundnessNotClaimed = true
```

This phase establishes the repository's executable package-refinement contract. It does not prove an unrestricted mathematical soundness theorem for every assertion-shaped field in a local package. Final theorem nodes remain quarantined.

The sealed `7072f8d` source/checker and artefact releases are not modified.

## Required package coordinates

The checker covers every theorem in:

```text
GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0
```

and therefore every node in:

```text
GLOBAL_PACKAGE_NODE_IDS0 = Package.<required theorem>
```

The required global package coordinates are:

```text
Package.E.VerifyDWSoundness
Package.N.TraceableNormalization
Package.Splice.BoundedAndComposed
Package.FT.FiniteTableCoverage
Package.X.CriticalWindowRouting
Package.BC.BranchCycleRouting
Package.UN.UnaryDecoderRouting
Package.HN.LeafTightness
Package.HResolve.GlobalHereditaryResolver
Package.BUD.BudgetResolver
Package.NORFF.FrontierFaithfulComparison
Package.RW.BCELReady
Package.BN2.SideTightCoherentOptimum
Package.BN3.SimultaneousEnvelope
Package.BN4.ActivationExact
Package.BN5.FullShadowLocalization
Package.PkgC.SeparatingConsumers
Package.BN6.HypergraphPacket
Package.Packet.SelectorSeeds
Package.R.SelectorRealization
Package.HB.NegativeClosure
Package.O.ZeroSlackOracle
Package.G.LockedNANDThreshold
Package.Final.FrameworkMatch
Package.PACK.PackageSufficiency
```

The local package inventory also contains the supporting `FTX` and `HNShape` families. They remain checked by `CheckLocalPackages0` and `CheckLocalPackageFamily0`, but they do not create additional global package-theorem coordinates.

## Semantic package checker

The new checker is:

```text
CheckGlobalPackageSemantic0
```

It accepts only `GlobalPackageSemanticInput0` records containing:

- a development-purpose reflection KBundle;
- the legacy global proof DAG;
- the accepted infrastructure semantic suite;
- the accepted row pack and locked-NAND row family;
- the accepted phase-35 row semantic suite;
- a complete local-package inventory;
- a generated `GlobalPackageSemanticSuite0`;
- the exact bounded scope and fail-closed package policy.

## Predecessor boundary

Before evaluating any package refinement, the checker reruns:

```text
CheckGlobalProofDAGRowSuccessor0
```

The predecessor must remain development-only and expose:

```text
kBundleFinalReady = true
semanticK0ConformanceReady = true
semanticSigmaReady = true
semanticReflectionReady = true
globalInfrastructureSemanticReady = true
globalRowDerivationsReady = true
globalPackageDerivationsReady = false
globalFinalDerivationsReady = false
activeFinalNodeIds = []
```

Its blocked package-node set must be exactly `GLOBAL_PACKAGE_NODE_IDS0`.

## Local package inventory boundary

The checker independently runs:

```text
CheckLocalPackages0
```

That checker must accept the full inventory, including the supporting `FTX` and `HNShape` packages. This preserves exact family coverage, local import acyclicity, forbidden-edge policy, bounds metadata, no-hidden-minimization scanning, absence of opaque proof blobs, local theorem alignment, and child-family checker acceptance.

The package semantic checker does not treat the inventory's assertion-shaped contract fields as self-authenticating mathematical proofs. It subjects every globally represented package to additional positive and negative executable probes.

## Digest-bound package suite

The generated suite is:

```text
GlobalPackageSemanticSuite0
```

It contains one `GlobalPackageSemanticBinding0` for each required global package theorem. Each binding includes:

```text
index
family
theorem
nodeId
globalNodeDigest
localPackageDigest
rowRefDigest
importsDigest
checkerContractDigest
bindingDigest
```

Every binding is recomputed from the exact global node, local package, local row reference, local import list, and versioned executable checker contract. Caller-added readiness or theorem-truth assertions are rejected.

## Global package-node contract

Every global package node must retain:

```text
nodeKind = package
id = Package.<theorem>
label = <theorem>
mode = Full
imports = []
payload = {}
conclusion = {
  tag: PackageTheoremAccepted0,
  theorem: <theorem>
}
```

Every package node has the exact infrastructure prerequisites:

```text
Bounds.Polynomial
NoMin.Global
Mode.Firewall
Import.Acyclic
```

`Package.G.LockedNANDThreshold` additionally requires:

```text
G.ThresholdCert.proof
```

Each package node must carry a positive polynomial bound no larger than the global bounds envelope. The empty payload prevents a caller from promoting a package coordinate with fields such as `sound = true` or `theoremTrue = true`.

## Row-to-package binding

Each global package theorem is mapped to its stable local package family through `LOCAL_PACKAGE_REQUIREMENTS0`.

The checker requires exactly one local row reference and binds it to:

```text
Row.<family>
```

The row reference must match the required batch, family, package, schema, and kind identifiers. The corresponding executable row digest must equal the digest carried by the accepted phase-35 semantic row derivation.

This prevents a package record from naming one row while inheriting readiness from a different row derivation.

## Local import binding

Every local import must resolve to a checked local package. Each semantic refinement records:

```text
imported family
imported theorem
imported local-package digest
whether a global package node represents the import
represented global package node id, when present
```

The `FTX` and `HNShape` imports are recorded as checked supporting packages even though they do not have separate global package-theorem nodes.

## Positive executable probe

For every global package theorem, the checker runs:

```text
CheckLocalPackageFamily0(localPackage)
```

The result must accept with:

```text
checker = CheckLocalPackageFamily0
NF.kind = LocalPackageFamily0NF
NF.family = required family
NF.theorem = required theorem
```

The accepted record digest is included in the package refinement.

## Negative theorem-identity probe

For every global package theorem, the checker changes only the local package's theorem identity and reruns:

```text
CheckLocalPackageFamily0(mutatedLocalPackage)
```

The result must reject at:

```text
Coord = CheckLocalPackageFamily0.identity
Path = [theorem]
```

The rejection record digest is included in the package refinement. This protects against disabled theorem-identity checks, stale family mappings, and checkers that accept an arbitrary theorem label.

The negative probe is not an unrestricted theorem-soundness proof. It establishes a concrete fail-closed executable contract for the exact version-zero package representation.

## Package refinement normal form

Each accepted package refinement records:

```text
family
theorem
nodeId
packageId
batchId
schemaId
proofRule
globalNodeDigest
localPackageDigest
rowRefDigest
importsDigest
checkerContractDigest
bindingDigest
rowDigest
rowDerivationDigest
importBindings
positiveNFKind
positiveRecordDigest
negativeCoord
negativePath
negativeRecordDigest
conclusionDigest
refinementDigest
```

The refinement conclusion explicitly states:

```text
positiveExecutableContractAccepted = true
negativeTheoremIdentityProbeRejected = true
rowReferenceBound = true
importDependenciesBound = true
boundedExecutablePackageRefinement = true
unrestrictedPackageTheoremSoundnessNotClaimed = true
```

## Successor global gate

The new successor is:

```text
GlobalProofDAGSemanticPackageSuccessor0
```

It reruns the phase-35 row predecessor, runs `CheckGlobalPackageSemantic0`, and rebuilds the semantic overlay.

All required package nodes move out of the structural-only set:

```text
semanticPackageNodeIds = GLOBAL_PACKAGE_NODE_IDS0
blockedPackageNodeIds = []
globalPackageDerivationsReady = true
```

The overlay preserves all previous kernel, Sigma, reflection, infrastructure, and row bindings.

Each package overlay binding includes:

```text
global node digest
package refinement digest
local package digest
semantic row derivation digest
positive checker-record digest
negative checker-record digest
checker-contract digest
refinement-conclusion digest
```

## Current readiness status

Ready scoped surfaces:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.InfrastructureDerivations
GlobalDAG.RowDerivations
GlobalDAG.PackageDerivations
```

Remaining blocker:

```text
GlobalDAG.FinalDerivations
```

The package readiness coordinate carries the bounded scope qualifiers above. It must not be cited as an unrestricted mathematical proof of every local package theorem.

## Final-node quarantine

The following nodes remain structural-only and quarantined:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

Development results remain:

```text
status = development-only
activeFinalNodeIds = []
legacyFinalNodesQuarantined = true
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

An explicit final-purpose package successor rejects while `GlobalDAG.FinalDerivations` remains blocked.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-global-package-semantic0.test.mjs \
  test/pcc-global-proof-dag-package-successor0.test.mjs
```

The tests cover:

- exact required global package-theorem coverage;
- positive local-family checker acceptance;
- negative theorem-identity rejection for every package;
- supporting `FTX` and `HNShape` package acceptance;
- row-reference and semantic row-digest binding;
- exact global package premises and conclusions;
- local import and forbidden-edge rejection;
- missing package-family rejection;
- caller readiness and stale binding rejection;
- activation of every package node in the semantic overlay;
- preservation of all earlier semantic bindings;
- continued final-node quarantine and disabled public theorem emission.

## Next step

The sole remaining global surface is final-node derivation.

That work must be split into explicit implications rather than activating all four final nodes from structural linkage. The first final layer should independently bind `Final.PackageSoundness` and `Final.GeneratedPackageSufficiency` to their executable antecedents and negative mutation probes. The SAT-in-P and P-versus-NP implication nodes should remain quarantined until their reduction, runtime, completeness, and complexity-theoretic assumptions are represented as independently reviewable semantic obligations.
