# Semantic kernel hardening — phase 30 (FiniteRel KBundle and global-gate integration)

## Purpose

Phase 29 implemented exact bounded `FiniteRel.verify` and completed primitive semantic-rule coverage at the successor KImpl boundary. Phase 30 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration remains layered and fail-closed. It reruns the merged TruthVec boundaries as predecessor checks, proves that the complete sixteen-rule KImpl is independently final-ready, and then keeps the wider bundle and global theorem surfaces closed because semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations are not yet implemented.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## FiniteRel successor KBundle

The new record is:

```text
KBundleSemanticFiniteRelSuccessor0
```

It contains a development-purpose `KImplSemanticFiniteRelSuccessor0`, the legacy conformance suite, Sigma registry, reflection registry, fixed checker binding, and fail-closed release policy.

### TruthVec predecessor preservation

`CheckKBundleFiniteRelSuccessor0` filters the complete semantic proof DAG to the fifteen predecessor families:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
```

It reconstructs and reruns `CheckKBundleTruthVecSuccessor0` over that sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
semanticKImplFinalReady = false
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and must expose exactly one missing primitive rule:

```text
FiniteRel
```

A predecessor acceptance record cannot be relabelled as FiniteRel readiness.

### Complete semantic KImpl

The checker independently runs:

```text
CheckKImplFiniteRelSuccessor0
CheckKImplFiniteRelFinalTheoremReadiness0
```

The development result must expose exactly the complete primitive rule set:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

and an empty primitive missing-rule list.

The development-purpose KImpl remains development-only, but its computed kernel-readiness field is true. The explicit final-purpose KImpl probe must accept with:

```text
semanticKernelReady = true
finalTheoremReady = true
publicTheoremEmissionAllowed = true
```

### Computed KBundle readiness

The FiniteRel successor KBundle recomputes four coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

`KImpl.SemanticRuleCoverage` is now ready and is bound to the digest returned by `CheckKImplFiniteRelFinalTheoremReadiness0`.

The remaining three coordinates stay blocked:

- the current conformance suite checks primitive names and record shape rather than semantic derivations;
- V53 and V54 remain registry entries rather than checked semantic-kernel derivations;
- reflection entries remain mappings rather than proof-producing checker refinements.

Therefore a development KBundle accepts only as development-only, and an explicit final-purpose KBundle rejects with exactly those three non-kernel blocker coordinates.

Caller readiness fields, a final-purpose child KImpl, stale TruthVec-only KImpl state, weakened policy, predecessor drift, and legacy structural failures reject.

## FiniteRel successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticFiniteRelSuccessor0
```

It contains the FiniteRel successor KBundle, the legacy global proof DAG, fixed checker binding, and a fail-closed final-node quarantine policy.

### TruthVec global-gate preservation

The checker filters the nested semantic proof DAG to the fifteen TruthVec-era rules, reconstructs the TruthVec successor KBundle, and reruns:

```text
CheckGlobalProofDAGTruthVecSuccessor0
```

The predecessor global gate must remain development-only, expose no active final node, preserve all final-node quarantine fields, recognize exactly the fifteen TruthVec-era kernel coordinates, and retain exactly one blocked kernel coordinate:

```text
K.FiniteRel
```

### Complete primitive semantic overlay

After the predecessor boundary accepts, the FiniteRel KBundle is checked and the semantic overlay is rebuilt. Every primitive kernel coordinate is now active:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
K.OblTopoInd
K.TraceInd
K.FiniteExhaust
K.DPInd
K.Hall
K.RankInd
K.MinCounterexample
K.IntArith
K.Transport
K.TruthVec
K.FiniteRel
```

The blocked primitive-kernel coordinate list is empty:

```text
blockedKernelNodeIds = []
primitiveSemanticRuleCoverageComplete = true
```

Sigma, reflection, row, package, and final nodes remain structural-only until represented by semantic derivations.

The four legacy final nodes remain quarantined:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

### Computed global gate

The derived gate contains:

```text
Gate.PredecessorGlobal.DevelopmentAcceptance
Gate.KBundle.FiniteRelDevelopmentAcceptance
Gate.KBundle.FiniteRelFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both FiniteRel KBundle final readiness and semantic global-node derivations. The KBundle branch remains false because K0, Sigma, and reflection are not semantically ready. The global semantic-node branch also remains false.

Development acceptance is therefore forced to record:

```text
status = development-only
activeFinalNodeIds = []
legacyFinalNodesQuarantined = true
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

## Current readiness status

Primitive semantic rule coverage is complete:

```text
missing primitive rules = []
```

The final theorem gate remains blocked by:

```text
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.SemanticNodeDerivations
```

Completing primitive-rule coverage is necessary but not sufficient for activating any public theorem node.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-finiterel-successor0.test.mjs \
  test/pcc-global-proof-dag-finiterel-successor0.test.mjs
```

The tests cover:

- exact fifteen-to-sixteen primitive rule expansion;
- preservation of the TruthVec predecessor boundaries;
- removal of `FiniteRel` and `K.FiniteRel` from the missing/blocked lists;
- acceptance of the explicit KImpl final-readiness probe;
- continued KBundle final rejection on the three non-kernel surfaces;
- KImpl and KBundle readiness-digest binding;
- caller readiness rejection;
- nested final-purpose child rejection;
- stale predecessor rejection;
- policy weakening rejection;
- propagation of Sigma and legacy global-DAG failures;
- complete primitive semantic overlay construction;
- continued quarantine of every legacy final theorem node.

## Next step

The next semantic surface is K0 semantic conformance.

A successor conformance checker should replace primitive-name and shape-only coverage with explicit local soundness obligations for each of the sixteen primitive rule checkers. It must bind every conformance item to the corresponding executable checker digest, prove the accepted normal-form contract, reject stale or caller-supplied soundness assertions, and remain separate from Sigma and reflection readiness.
