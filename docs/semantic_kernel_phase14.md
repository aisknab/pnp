# Semantic kernel hardening — phase 14 (FiniteExhaust KBundle and global-gate integration)

## Purpose

Phase 13 implemented exact `FiniteExhaust` semantics over an explicit canonical finite domain and added a FiniteExhaust-expanded successor KImpl. Phase 14 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration is layered and fail-closed. It does not rewrite the merged TraceInd boundaries and does not modify the sealed `7072f8d` source/checker or artefact release.

## Why this integration is required

A new primitive checker is not part of the final proof chain merely because its module exists. The wider chain must:

1. require the new checker rather than the predecessor checker;
2. rerun and preserve every predecessor boundary;
3. recompute final readiness rather than trust a nested result;
4. expand the global semantic overlay;
5. keep all legacy final theorem nodes quarantined.

Phase 14 supplies those links for `FiniteExhaust`.

## FiniteExhaust successor KBundle

The new record is:

```text
KBundleSemanticFiniteExhaustSuccessor0
```

It contains:

```text
Purpose
SemanticKImpl          KImplSemanticFiniteExhaustSuccessor0, development-purpose
K0                     legacy conformance suite
PSigma                 legacy Sigma registry
ReflectionRegistry     legacy reflection registry
Binding
Policy
```

### Predecessor preservation

`CheckKBundleFiniteExhaustSuccessor0` extracts the complete semantic proof DAG and filters it to:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
```

It reconstructs and runs `CheckKBundleTraceIndSuccessor0` over that filtered sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and must expose exactly the seven predecessor rules. This prevents the TraceInd boundary from being relabelled as FiniteExhaust readiness.

### Expanded semantic KImpl

The checker independently runs:

```text
CheckKImplFiniteExhaustSuccessor0
CheckKImplFiniteExhaustFinalTheoremReadiness0
```

The development record must expose exactly:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
```

The final probe remains rejected because eight primitive rule families are absent.

### Computed KBundle readiness

The successor KBundle recomputes these coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl coordinate is bound to the digest returned by `CheckKImplFiniteExhaustFinalTheoremReadiness0`. The other three remain blocked:

- the current conformance suite is structural-only;
- V53 and V54 remain registry entries rather than semantic derivations;
- reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale TraceInd-only KImpl records, and weakened policies reject.

## FiniteExhaust successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticFiniteExhaustSuccessor0
```

It contains the FiniteExhaust successor KBundle, the legacy global proof DAG, fixed checker bindings, and a fail-closed final-node quarantine policy.

### Predecessor global-gate preservation

The checker filters the nested semantic proof DAG to the seven predecessor rules, reconstructs the TraceInd successor KBundle, and reruns:

```text
CheckGlobalProofDAGTraceIndSuccessor0
```

That predecessor global gate must remain development-only, expose no active final node, quarantine every legacy final theorem coordinate, and recognize exactly:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
K.OblTopoInd
K.TraceInd
```

### Expanded semantic overlay

After the predecessor boundary accepts, the checker runs the FiniteExhaust successor KBundle and rebuilds the semantic overlay. The semantically implemented kernel coordinates become:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
K.OblTopoInd
K.TraceInd
K.FiniteExhaust
```

The remaining eight kernel coordinates are blocked. Every Sigma, reflection, row, package, and final node remains structural-only until represented by a semantic derivation.

The four legacy final nodes remain quarantined:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

### Computed global gate

The expanded derived gate contains:

```text
Gate.PredecessorGlobal.DevelopmentAcceptance
Gate.KBundle.FiniteExhaustDevelopmentAcceptance
Gate.KBundle.FiniteExhaustFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both:

```text
Gate.KBundle.FiniteExhaustFinalReadiness
Gate.GlobalDAG.SemanticNodeDerivations
```

The KBundle gate is tied to the expanded KBundle readiness digest. The global semantic-node gate remains false because the remaining kernel, Sigma, reflection, package, and final nodes have not been migrated.

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
```

Still missing:

```text
DPInd
Hall
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
  test/pcc-kbundle-finiteexhaust-successor0.test.mjs \
  test/pcc-global-proof-dag-finiteexhaust-successor0.test.mjs
```

The tests cover:

- preservation of the TraceInd KBundle and global-gate boundaries;
- exact expansion from seven to eight semantic kernel coordinates;
- removal of `FiniteExhaust` from the missing-rule list;
- final-purpose rejection with eight rules still missing;
- KImpl blocker binding to the FiniteExhaust final-probe digest;
- global-gate binding to the expanded KBundle readiness digest;
- quarantine of all four legacy final nodes;
- rejection of caller readiness assertions;
- rejection of nested final-purpose children;
- rejection of stale TraceInd-only KImpl or KBundle records;
- rejection of weakened policies;
- propagation of legacy Sigma and global-DAG structural failures.

## Next step

The next primitive semantic rule is `DPInd`.

Its checker must bind an explicit finite dynamic-programming state space, a well-founded evaluation order, exact base-state judgments, accepted recurrence instances, complete predecessor-state coverage, exact objective aggregation, and an exact terminal state theorem. After `DPInd` is accepted, the same integration pattern should carry its expanded KImpl through successor KBundle and global gates without weakening final-node quarantine.
