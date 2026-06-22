# Semantic kernel hardening — phase 18 (Hall KBundle and global-gate integration)

## Purpose

Phase 17 implemented `Hall.decide` over an explicit canonical finite bipartite graph and added a Hall-expanded successor KImpl. Phase 18 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration is layered and fail-closed. It preserves the merged DPInd boundaries as predecessor checks, does not activate any legacy final theorem node, and does not modify the sealed `7072f8d` source/checker or artefact release.

## Hall successor KBundle

The new record is:

```text
KBundleSemanticHallSuccessor0
```

It contains a development-purpose `KImplSemanticHallSuccessor0`, the legacy conformance suite, Sigma registry, reflection registry, fixed checker binding, and fail-closed policy.

### DPInd predecessor preservation

`CheckKBundleHallSuccessor0` filters the complete semantic proof DAG to:

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
```

It reconstructs and reruns `CheckKBundleDPIndSuccessor0` over that nine-rule sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and expose exactly the nine DPInd-era semantic rules. A predecessor acceptance record cannot be relabelled as Hall readiness.

### Hall-expanded semantic KImpl

The checker independently runs:

```text
CheckKImplHallSuccessor0
CheckKImplHallFinalTheoremReadiness0
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
```

The final probe remains rejected because six primitive rule families are still absent.

### Computed KBundle readiness

The Hall successor KBundle recomputes:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl blocker is bound to the digest returned by `CheckKImplHallFinalTheoremReadiness0`. The other three surfaces remain blocked because the current conformance suite is structural-only, V53/V54 remain registry entries rather than semantic derivations, and reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale DPInd-only KImpl state, weakened policy, predecessor drift, and legacy structural failures reject.

## Hall successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticHallSuccessor0
```

It contains the Hall successor KBundle, the legacy global proof DAG, fixed checker binding, and a fail-closed final-node quarantine policy.

### DPInd global-gate preservation

The checker filters the nested semantic proof DAG to the nine DPInd-era rules, reconstructs the DPInd successor KBundle, and reruns:

```text
CheckGlobalProofDAGDPIndSuccessor0
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
```

### Expanded semantic overlay

After the predecessor boundary accepts, the Hall KBundle is checked and the semantic overlay is rebuilt. The active semantic kernel coordinates become:

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
```

The blocked kernel coordinates fall from seven to six. Sigma, reflection, row, package, and final nodes remain structural-only until represented by semantic derivations.

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
Gate.KBundle.HallDevelopmentAcceptance
Gate.KBundle.HallFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both Hall KBundle final readiness and semantic global-node derivations. The KBundle branch is bound to the expanded KBundle readiness digest. The global semantic-node branch remains false.

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
```

Still missing:

```text
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

The final gate also remains blocked on semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-hall-successor0.test.mjs \
  test/pcc-global-proof-dag-hall-successor0.test.mjs
```

The tests cover exact nine-to-ten rule expansion, preservation of DPInd predecessor boundaries, removal of `Hall` from the missing-rule list, readiness-digest binding, final-purpose rejection, caller readiness rejection, stale predecessor rejection, policy weakening, propagation of Sigma and legacy global-DAG failures, semantic overlay expansion to `K.Hall`, and quarantine of all legacy final theorem nodes.

## Next step

The next primitive semantic rule is `RankInd`.

Its checker should bind an explicit finite ranked domain, exact base-rank cases, accepted local invariant evidence, strict rank decrease on every dependency, complete case coverage, and an exact terminal rank-induction judgment. Caller-supplied well-foundedness, rank-complete, or terminal-ready assertions must not be accepted.
