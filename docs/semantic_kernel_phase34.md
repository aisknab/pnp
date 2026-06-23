# Semantic kernel hardening — phase 34 (global infrastructure derivations)

## Purpose

Phase 33 completed the repository's scoped KBundle semantic surfaces through bounded executable reflection refinement. The reflection successor global gate still kept every non-kernel, non-Sigma, non-reflection global coordinate structural-only and exposed one aggregate blocker:

```text
GlobalDAG.SemanticNodeDerivations
```

Phase 34 starts that global migration in a deliberately narrow layer. It semantically derives the four global infrastructure coordinates:

```text
Bounds.Polynomial
NoMin.Global
Mode.Firewall
Import.Acyclic
```

Row, package, and final theorem nodes remain structural-only and quarantined.

This phase does not establish `P = NP`, does not activate a final theorem node, and does not modify the sealed `7072f8d` source/checker or artefact releases.

## Semantic infrastructure checker

The new checker is:

```text
CheckGlobalInfrastructureSemantic0
```

It accepts only a `GlobalInfrastructureSemanticInput0` containing:

- a development-purpose `KBundleSemanticReflectionSuccessor0`;
- the legacy `GlobalProofDAG0`;
- a generated `GlobalInfrastructureSemanticSuite0`;
- the exact fail-closed infrastructure policy.

Before deriving an infrastructure coordinate, the checker independently requires:

```text
CheckKBundleReflectionFinalTheoremReadiness0 = accept
CheckGlobalProofDAG0 = accept
```

Thus all scoped KBundle semantic surfaces must remain ready, and the legacy global graph must still satisfy its structural checks.

## Digest-bound infrastructure bindings

The generated suite contains one `GlobalInfrastructureSemanticBinding0` for each required coordinate. Every binding includes:

```text
index
coordinate
nodeId
nodeDigest
ledgerField
ledgerDigest
checkerContractDigest
conclusionDigest
bindingDigest
```

Bindings are recomputed from the exact global node, its matching global ledger, and a versioned executable contract. Caller-added readiness or truth fields are rejected.

## Polynomial-bounds derivation

`Bounds.Polynomial` must retain:

```text
nodeKind = bounds
premises = [K.IntArith, K.DPInd]
conclusion.tag = PolynomialBoundsAccepted0
```

The checker recomputes the global bounds envelope from `BoundsLedger` and every global node. It requires:

```text
BoundsLedger.kind = GlobalBoundsLedger0
BoundsLedger.polynomial = true
BoundsLedger.finite = true
BoundsLedger.exponent > 0
```

Every node must have a polynomial bounds record with a positive exponent no larger than the global exponent. The `Bounds.Polynomial` node must bind the exact global exponent.

The accepted derivation records the maximum node exponent, node count, finite-universe flag, and a digest of the complete node-bound summary.

## No-hidden-minimization derivation

`NoMin.Global` must retain:

```text
nodeKind = nomin
premises = [K.Record]
conclusion.tag = NoHiddenMinAccepted0
```

The ledger and node conclusion must bind the exact expansion roots:

```text
macros
aliases
generatedTemplates
imports
```

The ledger must bind the complete forbidden executable-symbol set. The checker recursively scans the full global DAG and treats executable keys such as `exec`, `call`, `program`, `body`, `operator`, generated bodies, and their aliases as executable positions. A forbidden minimization symbol in any such position rejects.

The accepted derivation records the scan counts and scan digest; it does not accept a caller assertion that the scan is clean.

## Mode-firewall derivation

`Mode.Firewall` must retain:

```text
nodeKind = mode
premises = [K.Transport]
conclusion.tag = ModeFirewallAccepted0
conclusion.quotientNotReplacement = true
```

The global mode ledger must enforce:

```text
quotientNotReplacement = true
constructiveFirewall = true
```

Every global node is classified as `Full` or `Quot`. A quotient node cannot carry a constructive full-replacement assertion, and package or final theorem nodes cannot be justified only in quotient mode.

The accepted derivation records the full/quotient node counts and a digest of the complete mode classification.

## Import-acyclicity derivation

`Import.Acyclic` must retain:

```text
nodeKind = import
premises = [K.DAGInd]
conclusion.tag = ImportGraphAccepted0
conclusion.acyclic = true
```

The node and `ImportGraph` must bind the exact forbidden package-edge policy. The checker independently:

- normalizes every explicit import edge;
- rejects self-import and forbidden package edges;
- checks the explicit package import graph for cycles;
- resolves every node premise and node import to a declared global node;
- checks the complete global dependency graph for cycles;
- records the verified topological order and edge digests.

## Successor global gate

The new successor is:

```text
GlobalProofDAGSemanticInfrastructureSuccessor0
```

It reruns the phase-33 predecessor:

```text
CheckGlobalProofDAGReflectionSuccessor0
```

The predecessor must remain development-only, expose no active final node, retain complete kernel/Sigma/reflection semantic coverage, and keep all four infrastructure coordinates in its structural-only set.

The successor then reruns:

```text
CheckKBundleReflectionSuccessor0
CheckKBundleReflectionFinalTheoremReadiness0
CheckGlobalInfrastructureSemantic0
```

The reflection KBundle final-readiness branch must remain ready.

## Expanded semantic overlay

The semantic overlay now activates:

```text
Bounds.Polynomial
NoMin.Global
Mode.Firewall
Import.Acyclic
```

Each infrastructure node is bound to:

```text
global node digest
semantic derivation digest
global ledger digest
executable checker-contract digest
derivation-conclusion digest
```

The overlay preserves all earlier kernel, Sigma, and reflection bindings.

Its readiness fields are:

```text
primitiveSemanticRuleCoverageComplete = true
semanticK0ConformanceReady = true
semanticSigmaReady = true
semanticReflectionReady = true
globalInfrastructureSemanticReady = true
globalRowDerivationsReady = false
globalPackageDerivationsReady = false
globalFinalDerivationsReady = false
globalSemanticNodeDerivationsReady = false
```

## Current readiness status

Ready scoped surfaces:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.InfrastructureDerivations
```

Remaining global sub-blockers:

```text
GlobalDAG.RowDerivations
GlobalDAG.PackageDerivations
GlobalDAG.FinalDerivations
```

All final theorem nodes remain quarantined:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

The active-final set remains empty and public theorem emission remains disabled.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-global-infrastructure-semantic0.test.mjs \
  test/pcc-global-proof-dag-infrastructure-successor0.test.mjs
```

The tests cover:

- exact four-coordinate derivation coverage;
- reflection predecessor preservation;
- reflection KBundle final-readiness preservation;
- node, ledger, checker-contract, and conclusion digest binding;
- bounds-envelope recomputation;
- hidden executable minimization rejection;
- quotient-only final-node rejection;
- explicit import-cycle rejection;
- malformed infrastructure premise and conclusion rejection;
- caller readiness and stale binding rejection;
- row/package/final blocker decomposition;
- continued final-node quarantine.

## Next step

The next layer is semantic global row derivation.

It should be split further rather than migrating every row in one change. A first row successor should derive the fixed infrastructure-facing row families and the three locked-NAND proof rows, bind them to their executable row checkers and accepted normal forms, and leave package and final theorem nodes quarantined. Package theorem derivations should begin only after all prerequisite row families are semantic and digest-bound.
