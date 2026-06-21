# Semantic kernel hardening — phase 12 (TraceInd KBundle and global-gate integration)

## Purpose

Phase 11 implemented exact topological `TraceInd` semantics and a TraceInd-expanded successor KImpl. Phase 12 carries that computed result through the successor KBundle and successor global proof-DAG gate.

The integration is layered and fail-closed. It preserves the merged OblTopoInd KBundle/global boundaries as executable predecessor checks and does not modify the sealed `7072f8d` source/checker or artefact release.

## Why this integration is required

A primitive checker is not part of the final proof chain merely because its module exists. The wider chain must:

1. require the new KImpl checker rather than the predecessor checker;
2. rerun and preserve every predecessor boundary;
3. recompute final readiness instead of trusting a nested record;
4. expand the global semantic overlay;
5. keep every legacy final theorem node quarantined.

Phase 12 supplies those links for `TraceInd`.

## TraceInd successor KBundle

The new record is:

```text
KBundleSemanticTraceIndSuccessor0
```

It contains:

```text
Purpose
SemanticKImpl          KImplSemanticTraceIndSuccessor0, development-purpose
K0                     legacy conformance suite
PSigma                 legacy Sigma registry
ReflectionRegistry     legacy reflection registry
Binding
Policy
```

### Predecessor preservation

`CheckKBundleTraceIndSuccessor0` extracts the complete semantic proof DAG and filters it to:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
```

It reconstructs and runs `CheckKBundleOblTopoIndSuccessor0` over that filtered sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and must expose exactly the six predecessor rules. This prevents the OblTopoInd boundary from being relabelled as TraceInd readiness.

### Expanded semantic KImpl

The checker independently runs:

```text
CheckKImplTraceIndSuccessor0
CheckKImplTraceIndFinalTheoremReadiness0
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
```

The final probe remains rejected because nine primitive rule families are absent.

### Computed KBundle readiness

The successor KBundle recomputes these coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl coordinate is bound to the digest returned by `CheckKImplTraceIndFinalTheoremReadiness0`. The other three remain blocked:

- the current conformance suite is structural-only;
- V53 and V54 remain registry entries rather than semantic derivations;
- reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale OblTopoInd-only KImpl records, and weakened policies reject.

## TraceInd successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticTraceIndSuccessor0
```

It contains the TraceInd successor KBundle, the legacy global proof DAG, fixed checker bindings, and a fail-closed final-node quarantine policy.

### Predecessor global-gate preservation

The checker filters the nested semantic proof DAG to the six predecessor rules, reconstructs the OblTopoInd successor KBundle, and reruns:

```text
CheckGlobalProofDAGOblTopoIndSuccessor0
```

That predecessor global gate must remain development-only, expose no active final node, quarantine every legacy final theorem coordinate, and recognize exactly:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
K.OblTopoInd
```

### Expanded semantic overlay

After the predecessor boundary accepts, the checker runs the TraceInd successor KBundle and rebuilds the semantic overlay. The semantically implemented kernel coordinates become:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
K.OblTopoInd
K.TraceInd
```

The remaining nine kernel coordinates are blocked. Every Sigma, reflection, row, package, and final node remains structural-only until represented by a semantic derivation.

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
Gate.KBundle.TraceIndDevelopmentAcceptance
Gate.KBundle.TraceIndFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both:

```text
Gate.KBundle.TraceIndFinalReadiness
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
```

Still missing:

```text
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

The final gate also remains blocked on semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-traceind-successor0.test.mjs \
  test/pcc-global-proof-dag-traceind-successor0.test.mjs
```

The tests cover:

- preservation of the OblTopoInd KBundle and global-gate boundaries;
- exact expansion from six to seven semantic kernel coordinates;
- removal of `TraceInd` from the missing-rule list;
- final-purpose rejection with nine rules still missing;
- KImpl blocker binding to the TraceInd final-probe digest;
- global-gate binding to the expanded KBundle readiness digest;
- quarantine of all four legacy final nodes;
- rejection of caller readiness assertions;
- rejection of nested final-purpose children;
- rejection of stale OblTopoInd-only KImpl or KBundle records;
- rejection of weakened policies;
- propagation of legacy Sigma and global-DAG structural failures.

## Next step

The next primitive semantic rule is `FiniteExhaust`.

Its checker must bind an explicit finite domain, canonical complete enumeration, accepted per-element cases, duplicate and omission rejection, exact domain cardinality, and a computed universal conclusion. After `FiniteExhaust` is accepted, the same integration pattern should carry its expanded KImpl through successor KBundle and global gates without weakening final-node quarantine.
