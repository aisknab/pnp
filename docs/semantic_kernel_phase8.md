# Semantic kernel hardening — phase 8 (LedgerInd KBundle and global-gate integration)

## Purpose

Phase 7 implemented exact finite `LedgerInd` semantics and a LedgerInd-expanded successor KImpl. Phase 8 carries that computed result through the successor KBundle and successor global proof-DAG gate.

The integration is intentionally layered. It does not rewrite the merged phase-6 boundaries, and it does not alter the sealed `7072f8d` source/checker or artefact release.

## Why this integration is separate

A new primitive-rule checker is not useful to the final proof chain merely because it exists. The wider chain must:

1. require the new checker rather than the older predecessor checker;
2. preserve every older structural and fail-closed boundary;
3. recompute final readiness instead of trusting a nested result;
4. update the global semantic overlay;
5. keep every legacy final theorem node quarantined.

Phase 8 supplies those links for `LedgerInd`.

## LedgerInd successor KBundle

The new record is:

```text
KBundleSemanticLedgerIndSuccessor0
```

It contains:

```text
Purpose
SemanticKImpl          KImplSemanticLedgerIndSuccessor0, development-purpose
K0                     legacy conformance suite
PSigma                 legacy Sigma registry
ReflectionRegistry     legacy reflection registry
Binding
Policy
```

### Predecessor preservation

`CheckKBundleLedgerIndSuccessor0` first extracts the complete semantic proof DAG and filters it to the predecessor rule set:

```text
Eq
Subst
Record
DAGInd
```

It then reconstructs and runs the phase-6 successor KBundle over that filtered sub-DAG. The predecessor KBundle must accept only as:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

Its exact supported-rule list must remain the four-rule predecessor set. This prevents the older boundary from being relabelled as evidence for `LedgerInd`.

### Expanded semantic KImpl

The checker independently runs:

```text
CheckKImplLedgerIndSuccessor0
CheckKImplLedgerIndFinalTheoremReadiness0
```

The development checker must expose exactly:

```text
Eq
Subst
Record
DAGInd
LedgerInd
```

The final checker remains rejected because eleven primitive rule families are still absent.

### Computed KBundle readiness

The successor KBundle recomputes the four readiness coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl coordinate is now bound to the digest of `CheckKImplLedgerIndFinalTheoremReadiness0`. The other three remain blocked:

- legacy conformance is structural-only;
- V53 and V54 are still registry entries rather than semantic derivations;
- reflection entries are still mapping-shaped rather than proof-producing refinement theorems.

The input cannot provide final-readiness booleans, missing-rule lists, a final-purpose child KImpl, or a weakened policy.

## LedgerInd successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticLedgerIndSuccessor0
```

It contains the LedgerInd successor KBundle, the legacy global proof DAG, fixed checker bindings, and a fail-closed final-node quarantine policy.

### Predecessor global-gate preservation

The checker filters the nested semantic proof DAG to the four-rule predecessor set, reconstructs the phase-6 KBundle, and reruns:

```text
CheckGlobalProofDAGSemanticSuccessor0
```

That predecessor global gate must remain development-only, expose no active final node, quarantine all four legacy final coordinates, and recognize only:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
```

### Expanded semantic overlay

After the predecessor boundary accepts, the checker runs the LedgerInd successor KBundle and rebuilds the semantic overlay. The semantically implemented kernel coordinates are now:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
K.LedgerInd
```

The remaining eleven kernel coordinates are blocked. Every Sigma, reflection, row, package, and final node remains structural-only until re-encoded as a semantic derivation.

The four required legacy final nodes remain quarantined:

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
Gate.KBundle.LedgerIndDevelopmentAcceptance
Gate.KBundle.LedgerIndFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both:

```text
Gate.KBundle.LedgerIndFinalReadiness
Gate.GlobalDAG.SemanticNodeDerivations
```

The KBundle gate is tied to the expanded KBundle readiness digest. The semantic global-node gate remains false because the package, Sigma, reflection, and final nodes have not yet been migrated.

Therefore development acceptance is forced to record:

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
```

Still missing:

```text
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

The final gate also remains blocked on semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-ledgerind-successor0.test.mjs \
  test/pcc-global-proof-dag-ledgerind-successor0.test.mjs
```

The tests cover:

- predecessor KBundle and predecessor global-gate preservation;
- exact expansion from four to five semantic kernel coordinates;
- removal of `LedgerInd` from the missing-rule list;
- final-purpose rejection with eleven rules still missing;
- exact KImpl blocker binding to the LedgerInd final-probe digest;
- exact global-gate binding to the expanded KBundle readiness digest;
- quarantine of all four legacy final nodes;
- rejection of caller readiness assertions;
- rejection of nested final-purpose children;
- rejection of stale DAGInd-only KImpl or phase-6 KBundle records;
- rejection of weakened policies;
- propagation of legacy Sigma and global-DAG structural failures.

## Next step

The next primitive semantic rule is `OblTopoInd`.

Its checker must model an explicit finite obligation graph and verify:

- exact obligation creation coordinates;
- canonical unique obligation IDs;
- dependency-topological order;
- permitted discharge rule families;
- full-mode discharge evidence where required;
- no discharge before all dependencies close;
- no duplicate, stale, or cross-mode discharge;
- exact terminal absence of open obligations.

After `OblTopoInd` is implemented, the same integration pattern should carry its expanded KImpl result into a new successor KBundle and global gate without weakening the quarantine policy.
