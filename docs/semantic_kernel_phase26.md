# Semantic kernel hardening — phase 26 (Transport KBundle and global-gate integration)

## Purpose

Phase 25 implemented checked `Transport.rename`, `Transport.project`, and `Transport.lift` over explicit finite carrier-coordinate fact bundles and added a Transport-expanded successor KImpl. Phase 26 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration remains layered and fail-closed. It reruns the merged IntArith boundaries as predecessor checks, does not activate any legacy final theorem node, and does not modify the sealed `7072f8d` source/checker or artefact release.

## Transport successor KBundle

The new record is:

```text
KBundleSemanticTransportSuccessor0
```

It contains a development-purpose `KImplSemanticTransportSuccessor0`, the legacy conformance suite, Sigma registry, reflection registry, fixed checker binding, and fail-closed policy.

### IntArith predecessor preservation

`CheckKBundleTransportSuccessor0` filters the complete semantic proof DAG to the thirteen predecessor families:

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
```

It reconstructs and reruns `CheckKBundleIntArithSuccessor0` over that sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and expose exactly the IntArith-era semantic rule set. A predecessor acceptance record cannot be relabelled as Transport readiness.

### Transport-expanded semantic KImpl

The checker independently runs:

```text
CheckKImplTransportSuccessor0
CheckKImplTransportFinalTheoremReadiness0
```

The development result must expose exactly:

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
```

The final probe remains rejected because two primitive rule families are still absent.

### Computed KBundle readiness

The Transport successor KBundle recomputes:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl blocker is bound to the digest returned by `CheckKImplTransportFinalTheoremReadiness0`. The other three surfaces remain blocked because the current conformance suite is structural-only, V53/V54 remain registry entries rather than semantic derivations, and reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale IntArith-only KImpl state, weakened policy, predecessor drift, and legacy structural failures reject.

## Transport successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticTransportSuccessor0
```

It contains the Transport successor KBundle, the legacy global proof DAG, fixed checker binding, and a fail-closed final-node quarantine policy.

### IntArith global-gate preservation

The checker filters the nested semantic proof DAG to the thirteen IntArith-era rules, reconstructs the IntArith successor KBundle, and reruns:

```text
CheckGlobalProofDAGIntArithSuccessor0
```

That predecessor global gate must remain development-only, expose no active final node, preserve all final-node quarantine fields, and recognize exactly:

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
```

### Expanded semantic overlay

After the predecessor boundary accepts, the Transport KBundle is checked and the semantic overlay is rebuilt. The active semantic kernel coordinates become:

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
```

The blocked primitive coordinates fall from three to two. Sigma, reflection, row, package, and final nodes remain structural-only until represented by semantic derivations.

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
Gate.KBundle.TransportDevelopmentAcceptance
Gate.KBundle.TransportFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both Transport KBundle final readiness and semantic global-node derivations. The KBundle branch is bound to the expanded KBundle readiness digest. The global semantic-node branch remains false.

Development acceptance is therefore forced to record:

```text
status = development-only
activeFinalNodeIds = []
legacyFinalNodesQuarantined = true
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

## Current rule status

Implemented semantic primitive families:

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
```

Still missing:

```text
TruthVec
FiniteRel
```

The final gate also remains blocked on semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-transport-successor0.test.mjs \
  test/pcc-global-proof-dag-transport-successor0.test.mjs
```

The tests cover exact thirteen-to-fourteen rule expansion, preservation of IntArith predecessor boundaries, removal of `Transport` from the missing-rule list, readiness-digest binding, final-purpose rejection, caller readiness rejection, stale predecessor rejection, policy weakening, propagation of Sigma and legacy global-DAG failures, semantic overlay expansion to `K.Transport`, and quarantine of all legacy final theorem nodes.

## Next step

The next primitive semantic rule is `TruthVec`.

Its checker should evaluate explicit bounded Boolean vectors independently, preserve input and output order, require exact assignment arity and domains, compute every vector bit from a canonical Boolean expression or NAND trace, and reject caller-supplied equality, completeness, normalization, solver, search, or oracle assertions.
