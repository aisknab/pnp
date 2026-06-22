# Semantic kernel hardening — phase 24 (IntArith KBundle and global-gate integration)

## Purpose

Phase 23 implemented exact bounded affine `IntArith.prove` checking and added an IntArith-expanded successor KImpl. Phase 24 carries that computed result through successor KBundle and successor global proof-DAG boundaries.

The integration remains layered and fail-closed. It reruns the merged MinCounterexample boundaries as predecessor checks, does not activate any legacy final theorem node, and does not modify the sealed `7072f8d` source/checker or artefact release.

## IntArith successor KBundle

The new record is:

```text
KBundleSemanticIntArithSuccessor0
```

It contains a development-purpose `KImplSemanticIntArithSuccessor0`, the legacy conformance suite, Sigma registry, reflection registry, fixed checker binding, and fail-closed policy.

### MinCounterexample predecessor preservation

`CheckKBundleIntArithSuccessor0` filters the complete semantic proof DAG to the twelve predecessor families:

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

It reconstructs and reruns `CheckKBundleMinCounterexampleSuccessor0` over that sub-DAG. The predecessor KBundle must remain:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

and expose exactly the MinCounterexample-era semantic rule set. A predecessor acceptance record cannot be relabelled as IntArith readiness.

### IntArith-expanded semantic KImpl

The checker independently runs:

```text
CheckKImplIntArithSuccessor0
CheckKImplIntArithFinalTheoremReadiness0
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
```

The final probe remains rejected because three primitive rule families are still absent.

### Computed KBundle readiness

The IntArith successor KBundle recomputes:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The KImpl blocker is bound to the digest returned by `CheckKImplIntArithFinalTheoremReadiness0`. The other three surfaces remain blocked because the current conformance suite is structural-only, V53/V54 remain registry entries rather than semantic derivations, and reflection entries remain mappings rather than proof-producing refinements.

Caller readiness fields, a final-purpose child KImpl, stale MinCounterexample-only KImpl state, weakened policy, predecessor drift, and legacy structural failures reject.

## IntArith successor global proof-DAG gate

The new record is:

```text
GlobalProofDAGSemanticIntArithSuccessor0
```

It contains the IntArith successor KBundle, the legacy global proof DAG, fixed checker binding, and a fail-closed final-node quarantine policy.

### MinCounterexample global-gate preservation

The checker filters the nested semantic proof DAG to the twelve MinCounterexample-era rules, reconstructs the MinCounterexample successor KBundle, and reruns:

```text
CheckGlobalProofDAGMinCounterexampleSuccessor0
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
```

### Expanded semantic overlay

After the predecessor boundary accepts, the IntArith KBundle is checked and the semantic overlay is rebuilt. The active semantic kernel coordinates become:

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

The blocked primitive coordinates fall from four to three. Sigma, reflection, row, package, and final nodes remain structural-only until represented by semantic derivations.

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
Gate.KBundle.IntArithDevelopmentAcceptance
Gate.KBundle.IntArithFinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both IntArith KBundle final readiness and semantic global-node derivations. The KBundle branch is bound to the expanded KBundle readiness digest. The global semantic-node branch remains false.

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
```

Still missing:

```text
Transport
TruthVec
FiniteRel
```

The final gate also remains blocked on semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-intarith-successor0.test.mjs \
  test/pcc-global-proof-dag-intarith-successor0.test.mjs
```

The tests cover exact twelve-to-thirteen rule expansion, preservation of MinCounterexample predecessor boundaries, removal of `IntArith` from the missing-rule list, readiness-digest binding, final-purpose rejection, caller readiness rejection, stale predecessor rejection, policy weakening, propagation of Sigma and legacy global-DAG failures, semantic overlay expansion to `K.IntArith`, and quarantine of all legacy final theorem nodes.

## Next step

The next primitive semantic rule is `Transport`.

Its checker should bind explicit source and target carriers or modes, an accepted source judgment, a declared transport map, every preservation obligation required by the judgment kind, and the exact computed target judgment. Quotient equality must remain nonconstructive unless a checked full lift and all lost-bit or finite-kernel obligations are discharged.
