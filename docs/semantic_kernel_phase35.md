# Semantic kernel hardening — phase 35 (bounded global row-coordinate contracts)

## Purpose

Phase 34 activated semantic derivations for the four global infrastructure coordinates and decomposed the remaining global blocker into row, package, and final sub-surfaces.

Phase 35 takes the next fail-closed step by binding every required global row coordinate—including the three locked-NAND proof rows—to an exact versioned coordinate contract and the live global node record.

This is deliberately narrower than a theorem-soundness result. Accepted records state:

```text
boundedGlobalRowCoordinateContractsOnly = true
unrestrictedRowTheoremSoundnessNotClaimed = true
```

The layer proves that the global row coordinates, prerequisites, conclusions, payloads, bounds, and dependency order have not drifted. It does not yet prove the mathematical soundness of every row theorem. Package and final nodes remain quarantined.

The sealed `7072f8d` source/checker and artefact releases are not modified.

## Required row coordinates

The checker covers all generic row-family coordinates:

```text
Row.<family>
```

for every `ROW_REQUIRED_FAMILIES0` entry, plus the locked-NAND proof chain:

```text
G.BaselineCert.proof
G.TraceCert.proof
G.ThresholdCert.proof
```

The required coordinate set is exported as:

```text
GLOBAL_ROW_SEMANTIC_NODE_IDS0
```

## Digest-bound row suite

The generated suite is:

```text
GlobalRowsSemanticSuite0
```

It contains one `GlobalRowSemanticBinding0` per required coordinate. Each binding records:

```text
index
coordinate
nodeId
nodeDigest
premiseDigest
conclusionDigest
payloadDigest
boundsDigest
checkerContractDigest
bindingDigest
```

Every field is recomputed from the live global node and the versioned coordinate contract. Caller-added fields such as `sound`, `theoremTrue`, `complete`, or `ready` are rejected.

## Predecessor boundary

`CheckGlobalRowsSemantic0` reruns:

```text
CheckGlobalProofDAGInfrastructureSuccessor0
```

The predecessor must remain development-only and must expose:

```text
globalInfrastructureSemanticReady = true
globalRowDerivationsReady = false
globalPackageDerivationsReady = false
globalFinalDerivationsReady = false
activeFinalNodeIds = []
```

Its blocked row set must be exactly the complete required row-coordinate set.

## Generic row-family contracts

Every generic row coordinate must retain:

```text
nodeKind = row
id = Row.<family>
label = <family>
premises = [K.Record, K.Transport]
imports = []
mode = Full
conclusion = {
  tag: RowFamilyAccepted0,
  family: <family>
}
payload = {}
```

The node must carry a positive polynomial exponent no larger than the global bounds envelope. Every prerequisite must resolve to an earlier global node.

A generic row payload is intentionally empty. A caller cannot promote a coordinate by inserting a theorem-truth or readiness flag.

## Locked-NAND baseline row

`G.BaselineCert.proof` must retain the exact contract:

```text
premises = [K.Record, K.DAGInd]
rowKind = BaselineCert
theorem = BaselineDistinct
rule = BaselineDistinctDirectWire0
derivationKind = BaselineDerivation0
directWireOutputConvention = true
lowerBoundRuleApplied = true
transparentProof = true
bounds.exponent = 4
```

Its proof reference must close back to the same coordinate.

## Locked-NAND trace row

`G.TraceCert.proof` must retain:

```text
premises = [K.Record, K.TraceInd]
rowKind = TraceCert
theorem = TraceCoherence
rule = NANDTraceCoherence0
derivationKind = TraceDerivation0
topologicalInduction = true
traceCoherent = true
transparentProof = true
bounds.exponent = 4
```

Its proof reference must also close to its own coordinate.

## Locked-NAND threshold row

`G.ThresholdCert.proof` must retain:

```text
premises = [
  G.BaselineCert.proof,
  G.TraceCert.proof,
  K.IntArith
]
rowKind = ThresholdCert
theorem = LockedNANDThreshold
rule = LockedNANDThreshold0
derivationKind = ThresholdDerivation0
baselineDerivation = G.BaselineCert.proof
traceDerivation = G.TraceCert.proof
residualSlackMax = 4
finalOutputGates = 4
satIffMinAboveBaseline = true
unsatMinEqualsBaseline = true
transparentProof = true
bounds.exponent = 4
```

The checker independently closes the exact baseline/trace dependency names and the equality:

```text
residualSlackMax = finalOutputGates = 4
```

This verifies the versioned global coordinate contract. It does not, by itself, establish the underlying locked-NAND theorem for every instance.

## Successor global gate

The new successor is:

```text
GlobalProofDAGSemanticRowsSuccessor0
```

It reruns the phase-34 infrastructure predecessor, runs `CheckGlobalRowsSemantic0`, and rebuilds the semantic overlay.

All row nodes move out of the structural-only set and receive digest-bound coordinate bindings:

```text
semanticRowNodeIds = GLOBAL_ROW_SEMANTIC_NODE_IDS0
blockedRowNodeIds = []
globalRowCoordinateDerivationsReady = true
```

The earlier kernel, Sigma, reflection, and infrastructure bindings are preserved.

## Readiness decomposition

The computed gate distinguishes coordinate readiness from theorem soundness:

```text
Gate.GlobalDAG.RowCoordinateContracts = ready
Gate.GlobalDAG.RowTheoremDerivations = blocked
```

The remaining blockers are:

```text
GlobalDAG.RowTheoremDerivations
GlobalDAG.PackageDerivations
GlobalDAG.FinalDerivations
```

The row-theorem blocker remains because this phase does not bind each row family to an independently checked executable theorem derivation.

## Final-node quarantine

The following nodes remain quarantined:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

Accepted development results remain:

```text
status = development-only
activeFinalNodeIds = []
legacyFinalNodesQuarantined = true
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

An explicit final-purpose record rejects.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-global-rows-semantic0.test.mjs \
  test/pcc-global-proof-dag-rows-successor0.test.mjs
```

The tests cover:

- complete generic and locked-NAND coordinate coverage;
- exact prerequisite and conclusion contracts;
- Full-mode and polynomial-envelope enforcement;
- rejection of caller theorem/readiness payloads;
- locked-NAND dependency-chain preservation;
- stale node/contract digest rejection;
- infrastructure predecessor preservation;
- activation of every row coordinate in the semantic overlay;
- explicit separation between row-coordinate readiness and row-theorem soundness;
- continued package/final blocking and final-node quarantine.

## Next step

The next layer must address `GlobalDAG.RowTheoremDerivations` rather than relabelling coordinate acceptance as theorem soundness.

That work should bind each required row family to its executable row checker, canonical accepted normal form, negative mutation probes, and any finite witness ledger needed by the theorem. It should be split into reviewable families. The first theorem layer should cover the fixed foundational row families and the three locked-NAND proof rows; package theorem nodes must remain blocked until all of their prerequisite row theorems have independent executable derivations.
