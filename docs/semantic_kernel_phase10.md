# Semantic kernel hardening — phase 10 (OblTopoInd KBundle and global-gate integration)

## Purpose

Phase 9 implemented exact `OblTopoInd` lifecycle semantics and an OblTopoInd-expanded successor KImpl. Phase 10 carries that computed result through the successor KBundle and successor global proof-DAG gate.

The integration is layered and fail-closed. It does not rewrite the merged LedgerInd boundaries and does not modify the sealed `7072f8d` source/checker or artefact release.

## Why this integration is required

A primitive-rule checker is not part of the final proof chain merely because its module exists. The wider chain must:

1. require the new checker instead of the predecessor checker;
2. rerun and preserve every predecessor boundary;
3. recompute final readiness rather than trust a nested result;
4. expand the global semantic overlay;
5. keep every legacy final theorem node quarantined.

Phase 10 supplies those links for `OblTopoInd`.

## OblTopoInd successor KBundle

The new record is:

```text
KBundleSemanticOblTopoIndSuccessor0
```

It contains:

```text
Purpose
SemanticKImpl          KImplSemanticOblTopoIndSuccessor0, development-purpose
K0                     legacy conformance suite
PSigma                 legacy Sigma registry
ReflectionRegistry     legacy reflection registry
Binding
Policy
```

### Predecessor preservation

`CheckKBundleOblTopoIndSuccessor0` extracts the complete semantic proof DAG and filters it to:

```text
Eq
Subst
Record
DAGInd
LedgerInd
```

It reconstructs and runs `CheckKBundleLedgerIndSuccessor0` over that filtered sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and must expose exactly the five predecessor rules. This prevents the LedgerInd boundary from being relabelled as OblTopoInd readiness.

### Expanded semantic KImpl

The checker independently runs:

```text
CheckKImplOblTopoIndSuccessor0
CheckKImplOblTopoIndFinalTheoremReadiness0
```

The development record must expose exactly:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
```

The final probe remains rejected because ten primitive rule families are absent.

### Computed KBundle readiness

The successor KBundle recomputes these coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl coordinate is bound to the digest returned by `CheckKImplOblTopoIndFinalTheoremReadiness0`. The other three remain blocked:

- the current conformance suite is structural-only;
- V53 and V54 remain registry entries rather than semantic derivations;
- reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale LedgerInd-only KImpl records, and weakened policies reject.

## OblTopoInd successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticOblTopoIndSuccessor0
```

It contains the OblTopoInd successor KBundle, the legacy global proof DAG, fixed checker bindings, and a fail-closed final-node quarantine policy.

### Predecessor global-gate preservation

The checker filters the nested semantic proof DAG to the five predecessor rules, reconstructs the LedgerInd successor KBundle, and reruns:

```text
CheckGlobalProofDAGLedgerIndSuccessor0
```

That predecessor global gate must remain development-only, expose no active final node, quarantine every legacy final theorem coordinate, and recognize exactly:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
```

### Expanded semantic overlay

After the predecessor boundary accepts, the checker runs the OblTopoInd successor KBundle and rebuilds the semantic overlay. The semantically implemented kernel coordinates become:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
K.OblTopoInd
```

The remaining ten kernel coordinates are blocked. Every Sigma, reflection, row, package, and final node remains structural-only until it is represented by a semantic derivation.

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
Gate.KBundle.OblTopoIndDevelopmentAcceptance
Gate.KBundle.OblTopoIndFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both:

```text
Gate.KBundle.OblTopoIndFinalReadiness
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
```

Still missing:

```text
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

The final gate also remains blocked on semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-obltopoind-successor0.test.mjs \
  test/pcc-global-proof-dag-obltopoind-successor0.test.mjs
```

The tests cover:

- preservation of the LedgerInd KBundle and global-gate boundaries;
- exact expansion from five to six semantic kernel coordinates;
- removal of `OblTopoInd` from the missing-rule list;
- final-purpose rejection with ten rules still missing;
- KImpl blocker binding to the OblTopoInd final-probe digest;
- global-gate binding to the expanded KBundle readiness digest;
- quarantine of all four legacy final nodes;
- rejection of caller readiness assertions;
- rejection of nested final-purpose children;
- rejection of stale LedgerInd-only KImpl or KBundle records;
- rejection of weakened policies;
- propagation of legacy Sigma and global-DAG structural failures.

## Next step

The next primitive semantic rule is `TraceInd`.

Its checker must bind an explicit finite topological trace, exact source and NAND-gate equations, accepted local transition evidence, declared output-coordinate identity, and an exact terminal trace judgment. After `TraceInd` is accepted, the same integration pattern should carry its expanded KImpl through successor KBundle and global gates without weakening final-node quarantine.
