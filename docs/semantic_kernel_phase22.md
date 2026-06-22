# Semantic kernel hardening — phase 22 (MinCounterexample KBundle and global-gate integration)

## Purpose

Phase 21 implemented `MinCounterexample.select` over an explicit finite canonical candidate domain and added a MinCounterexample-expanded successor KImpl. Phase 22 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration is layered and fail-closed. It preserves the merged RankInd boundaries as predecessor checks, does not activate any legacy final theorem node, and does not modify the sealed `7072f8d` source/checker or artefact release.

## MinCounterexample successor KBundle

The new record is:

```text
KBundleSemanticMinCounterexampleSuccessor0
```

It contains a development-purpose `KImplSemanticMinCounterexampleSuccessor0`, the legacy conformance suite, Sigma registry, reflection registry, fixed checker binding, and fail-closed policy.

### RankInd predecessor preservation

`CheckKBundleMinCounterexampleSuccessor0` filters the complete semantic proof DAG to:

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
```

It reconstructs and reruns `CheckKBundleRankIndSuccessor0` over that eleven-rule sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and expose exactly the RankInd-era semantic rule set. A predecessor acceptance record cannot be relabelled as MinCounterexample readiness.

### MinCounterexample-expanded semantic KImpl

The checker independently runs:

```text
CheckKImplMinCounterexampleSuccessor0
CheckKImplMinCounterexampleFinalTheoremReadiness0
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
```

The final probe remains rejected because four primitive rule families are still absent.

### Computed KBundle readiness

The successor KBundle recomputes:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl blocker is bound to the digest returned by `CheckKImplMinCounterexampleFinalTheoremReadiness0`. The other three surfaces remain blocked because the current conformance suite is structural-only, V53/V54 remain registry entries rather than semantic derivations, and reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale RankInd-only KImpl state, weakened policy, predecessor drift, and legacy structural failures reject.

## MinCounterexample successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticMinCounterexampleSuccessor0
```

It contains the MinCounterexample successor KBundle, the legacy global proof DAG, fixed checker binding, and a fail-closed final-node quarantine policy.

### RankInd global-gate preservation

The checker filters the nested semantic proof DAG to the eleven RankInd-era rules, reconstructs the RankInd successor KBundle, and reruns:

```text
CheckGlobalProofDAGRankIndSuccessor0
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
```

### Expanded semantic overlay

After the predecessor boundary accepts, the MinCounterexample KBundle is checked and the semantic overlay is rebuilt. The active semantic kernel coordinates become:

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
```

The blocked kernel coordinates fall from five to four. Sigma, reflection, row, package, and final nodes remain structural-only until represented by semantic derivations.

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
Gate.KBundle.MinCounterexampleDevelopmentAcceptance
Gate.KBundle.MinCounterexampleFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both MinCounterexample KBundle final readiness and semantic global-node derivations. The KBundle branch is bound to the expanded KBundle readiness digest. The global semantic-node branch remains false.

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
```

Still missing:

```text
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
  test/pcc-kbundle-mincounterexample-successor0.test.mjs \
  test/pcc-global-proof-dag-mincounterexample-successor0.test.mjs
```

The tests cover exact eleven-to-twelve rule expansion, preservation of RankInd predecessor boundaries, removal of `MinCounterexample` from the missing-rule list, readiness-digest binding, final-purpose rejection, caller readiness rejection, stale predecessor rejection, policy weakening, propagation of Sigma and legacy global-DAG failures, semantic overlay expansion to `K.MinCounterexample`, and quarantine of all legacy final theorem nodes.

## Next step

The next primitive semantic rule is `IntArith`.

Its checker should evaluate explicit bounded integer expressions with overflow-safe arithmetic, verify canonical comparison and equality judgments, consume only accepted arithmetic premises, and reject hidden optimization, minimization, solver, search, or oracle calls. Any certificate format must make every arithmetic identity replayable rather than accepting caller-provided truth flags.
