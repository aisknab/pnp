# Semantic kernel hardening — phase 20 (RankInd KBundle and global-gate integration)

## Purpose

Phase 19 implemented `RankInd.close` over an explicit finite fixed-arity lexicographic rank domain and added a RankInd-expanded successor KImpl. Phase 20 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration is layered and fail-closed. It preserves the merged Hall boundaries as predecessor checks, does not activate any legacy final theorem node, and does not modify the sealed `7072f8d` source/checker or artefact release.

## RankInd successor KBundle

The new record is:

```text
KBundleSemanticRankIndSuccessor0
```

It contains a development-purpose `KImplSemanticRankIndSuccessor0`, the legacy conformance suite, Sigma registry, reflection registry, fixed checker binding, and fail-closed policy.

### Hall predecessor preservation

`CheckKBundleRankIndSuccessor0` filters the complete semantic proof DAG to:

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

It reconstructs and reruns `CheckKBundleHallSuccessor0` over that ten-rule sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and expose exactly the ten Hall-era semantic rules. A predecessor acceptance record cannot be relabelled as RankInd readiness.

### RankInd-expanded semantic KImpl

The checker independently runs:

```text
CheckKImplRankIndSuccessor0
CheckKImplRankIndFinalTheoremReadiness0
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
```

The final probe remains rejected because five primitive rule families are still absent.

### Computed KBundle readiness

The RankInd successor KBundle recomputes:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl blocker is bound to the digest returned by `CheckKImplRankIndFinalTheoremReadiness0`. The other three surfaces remain blocked because the current conformance suite is structural-only, V53/V54 remain registry entries rather than semantic derivations, and reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale Hall-only KImpl state, weakened policy, predecessor drift, and legacy structural failures reject.

## RankInd successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticRankIndSuccessor0
```

It contains the RankInd successor KBundle, the legacy global proof DAG, fixed checker binding, and a fail-closed final-node quarantine policy.

### Hall global-gate preservation

The checker filters the nested semantic proof DAG to the ten Hall-era rules, reconstructs the Hall successor KBundle, and reruns:

```text
CheckGlobalProofDAGHallSuccessor0
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
```

### Expanded semantic overlay

After the predecessor boundary accepts, the RankInd KBundle is checked and the semantic overlay is rebuilt. The active semantic kernel coordinates become:

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

The blocked kernel coordinates fall from six to five. Sigma, reflection, row, package, and final nodes remain structural-only until represented by semantic derivations.

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
Gate.KBundle.RankIndDevelopmentAcceptance
Gate.KBundle.RankIndFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both RankInd KBundle final readiness and semantic global-node derivations. The KBundle branch is bound to the expanded KBundle readiness digest. The global semantic-node branch remains false.

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
```

Still missing:

```text
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
  test/pcc-kbundle-rankind-successor0.test.mjs \
  test/pcc-global-proof-dag-rankind-successor0.test.mjs
```

The tests cover exact ten-to-eleven rule expansion, preservation of Hall predecessor boundaries, removal of `RankInd` from the missing-rule list, readiness-digest binding, final-purpose rejection, caller readiness rejection, stale predecessor rejection, policy weakening, propagation of Sigma and legacy global-DAG failures, semantic overlay expansion to `K.RankInd`, and quarantine of all legacy final theorem nodes.

## Next step

The next primitive semantic rule is `MinCounterexample`.

Its checker should bind an explicit finite candidate domain and a canonical checked order, compute the least failing candidate, require accepted evidence that every earlier candidate satisfies the property, require accepted failure evidence at the selected candidate, and compute the terminal minimal-counterexample judgment. Caller-supplied minimality, `least = true`, search, solver, or oracle assertions must not be accepted.
