# Semantic kernel hardening — phase 16 (DPInd KBundle and global-gate integration)

## Purpose

Phase 15 implemented exact structural `DPInd` semantics over an explicit finite state graph and added a DPInd-expanded successor KImpl. Phase 16 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration is layered and fail-closed. It does not rewrite the merged FiniteExhaust boundaries and does not modify the sealed `7072f8d` source/checker or artefact release.

## Why this integration is required

A primitive checker does not become part of the final proof chain merely because its module exists. The wider chain must:

1. require the new checker rather than the predecessor checker;
2. rerun and preserve every predecessor boundary;
3. recompute final readiness rather than trust a nested result;
4. expand the global semantic overlay;
5. keep every legacy final theorem node quarantined.

Phase 16 supplies those links for `DPInd`.

## DPInd successor KBundle

The new record is:

```text
KBundleSemanticDPIndSuccessor0
```

It contains:

```text
Purpose
SemanticKImpl          KImplSemanticDPIndSuccessor0, development-purpose
K0                     legacy conformance suite
PSigma                 legacy Sigma registry
ReflectionRegistry     legacy reflection registry
Binding
Policy
```

### Predecessor preservation

`CheckKBundleDPIndSuccessor0` extracts the complete semantic proof DAG and filters it to:

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

It reconstructs and runs `CheckKBundleFiniteExhaustSuccessor0` over that filtered sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and must expose exactly the eight predecessor rules. This prevents the FiniteExhaust boundary from being relabelled as DPInd readiness.

### Expanded semantic KImpl

The checker independently runs:

```text
CheckKImplDPIndSuccessor0
CheckKImplDPIndFinalTheoremReadiness0
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
DPInd
```

The final probe remains rejected because seven primitive rule families are absent.

### Computed KBundle readiness

The successor KBundle recomputes these coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl coordinate is bound to the digest returned by `CheckKImplDPIndFinalTheoremReadiness0`. The other three remain blocked:

- the current conformance suite is structural-only;
- V53 and V54 remain registry entries rather than semantic derivations;
- reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale FiniteExhaust-only KImpl records, and weakened policies reject.

## DPInd successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticDPIndSuccessor0
```

It contains the DPInd successor KBundle, the legacy global proof DAG, fixed checker bindings, and a fail-closed final-node quarantine policy.

### Predecessor global-gate preservation

The checker filters the nested semantic proof DAG to the eight predecessor rules, reconstructs the FiniteExhaust successor KBundle, and reruns:

```text
CheckGlobalProofDAGFiniteExhaustSuccessor0
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
K.FiniteExhaust
```

### Expanded semantic overlay

After the predecessor boundary accepts, the checker runs the DPInd successor KBundle and rebuilds the semantic overlay. The semantically implemented kernel coordinates become:

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

The remaining seven kernel coordinates are blocked. Every Sigma, reflection, row, package, and final node remains structural-only until represented by a semantic derivation.

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
Gate.KBundle.DPIndDevelopmentAcceptance
Gate.KBundle.DPIndFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both:

```text
Gate.KBundle.DPIndFinalReadiness
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
DPInd
```

Still missing:

```text
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
  test/pcc-kbundle-dpind-successor0.test.mjs \
  test/pcc-global-proof-dag-dpind-successor0.test.mjs
```

Positive and rejection cases are kept in those canonical module test files. This preserves the release-audit test-to-module inventory: no standalone test filename is allowed to imply a nonexistent sibling implementation module.

The tests cover predecessor preservation, exact expansion from eight to nine semantic kernel coordinates, removal of `DPInd` from the missing-rule list, final-purpose rejection, readiness-digest binding, caller readiness rejection, stale predecessor rejection, policy weakening, and final-node quarantine.

## Next step

The next primitive semantic rule is `Hall`.

Its checker must bind an explicit finite bipartite graph, canonical left and right vertex sets, exact neighbourhood computation, accepted edge evidence, either a complete injective matching or an exact Hall-deficient subset, and a computed terminal matching or deficiency judgment. It must not accept a caller-supplied `matchingComplete` flag or an unchecked deficient-set claim.
