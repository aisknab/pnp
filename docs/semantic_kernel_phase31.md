# Semantic kernel hardening — phase 31 (semantic K0 conformance)

## Purpose

Phase 30 carried complete `FiniteRel` primitive coverage through the successor KBundle and global proof-DAG gates. The remaining bundle/global blockers were:

```text
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.SemanticNodeDerivations
```

Phase 31 implements the next semantic surface: K0 semantic conformance.

This phase upgrades the legacy K0 conformance suite from primitive-name and shape coverage into a checked semantic conformance surface. It does not alter Sigma or reflection readiness, does not activate final theorem nodes, and does not modify the sealed `7072f8d` source/checker or artefact release.

## Semantic K0 conformance checker

The new checker is:

```text
CheckSemanticK0Conformance0
```

It accepts only records of kind:

```text
SemanticK0ConformanceInput0
```

with:

- a `KImplSemanticFiniteRelSuccessor0` input;
- a legacy `KConformance0` suite;
- a generated `SemanticK0ConformanceSuite0`;
- the exact fail-closed semantic K0 conformance policy.

### Preconditions

The checker independently requires:

```text
CheckKImplFiniteRelFinalTheoremReadiness0 = accept
CheckConformance0 = accept
```

The first condition proves complete primitive semantic-rule coverage at the KImpl boundary. The second condition consumes the legacy structural K0 conformance suite before upgrading it.

A stale TruthVec-only KImpl, a malformed K0 suite, or missing legacy primitive coverage rejects before semantic K0 readiness is emitted.

### Local rule-conformance obligations

The semantic conformance suite contains one obligation for each primitive rule:

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
TruthVec
FiniteRel
```

Each obligation is:

```text
SemanticK0RuleConformance0(
  index,
  ruleName,
  conformanceNodeId,
  conformanceNodeDigest,
  primitiveChecker,
  proofChecker,
  finalProofChecker,
  kImplFinalReadinessChecker,
  acceptedNFKind,
  localSoundnessContract,
  executableBoundaryDigest,
  obligationDigest
)
```

The checker recomputes every obligation from the legacy K0 node and the executable semantic checker boundary. It rejects any caller-edited primitive checker name, proof checker name, accepted normal-form kind, digest, index, rule name, conformance-node digest, local contract, or extra soundness field.

### Contract boundary

The local soundness contract records:

- the primitive rule name;
- the semantic layer;
- the primitive checker boundary;
- the combined `CheckSemanticKernelProofFiniteRel0` final proof checker boundary;
- the `CheckKImplFiniteRelFinalTheoremReadiness0` final-readiness boundary;
- the accepted normal-form kind;
- total accept/reject behavior;
- accepted normal-form digest binding;
- fail-closed unsupported input behavior;
- no opaque proof objects;
- no hidden minimization or oracle;
- rejection of caller-supplied soundness assertions.

The checker does not accept a claim such as `sound = true`. Soundness is represented only by the computed binding to executable checker boundaries and accepted normal-form contracts.

## KBundle integration

The new successor KBundle is:

```text
KBundleSemanticK0ConformanceSuccessor0
```

It preserves the FiniteRel predecessor boundary by rerunning:

```text
CheckKBundleFiniteRelSuccessor0
```

on the complete primitive semantic sub-DAG. The predecessor must remain development-only and must still expose:

```text
semanticConformanceReady = false
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

The expanded KBundle then runs:

```text
CheckKImplFiniteRelSuccessor0
CheckSemanticK0Conformance0
```

and records:

```text
KImpl.SemanticRuleCoverage = ready
K0.SemanticConformance = ready
Sigma.SemanticDerivations = blocked
Reflection.SemanticSoundness = blocked
```

The accepted development record remains:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

An explicit final-purpose KBundle rejects because Sigma and reflection are still non-semantic surfaces.

## Global proof-DAG integration

The new successor global gate is:

```text
GlobalProofDAGSemanticK0ConformanceSuccessor0
```

It preserves the FiniteRel global predecessor by rerunning:

```text
CheckGlobalProofDAGFiniteRelSuccessor0
```

The predecessor global gate must remain development-only, expose no active final theorem node, preserve all final-node quarantine fields, and expose complete primitive kernel coverage with no blocked primitive kernel coordinate.

The expanded global semantic overlay records:

```text
primitiveSemanticRuleCoverageComplete = true
semanticK0ConformanceReady = true
semanticSigmaReady = false
semanticReflectionReady = false
globalSemanticNodeDerivationsReady = false
```

All primitive kernel coordinates remain active:

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
K.TruthVec
K.FiniteRel
```

The four legacy final theorem nodes remain quarantined:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

## Current readiness status

Ready semantic surfaces:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
```

Remaining blockers:

```text
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.SemanticNodeDerivations
```

No final theorem node is activated in this phase.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-k0-semantic-conformance0.test.mjs \
  test/pcc-kbundle-k0conformance-successor0.test.mjs \
  test/pcc-global-proof-dag-k0conformance-successor0.test.mjs
```

The tests cover exact sixteen-rule K0 obligation generation, binding to legacy conformance-node digests, binding to executable checker boundary digests, stale checker-name rejection, caller soundness-field rejection, missing legacy coverage rejection, stale KImpl rejection, FiniteRel predecessor preservation, KBundle/global final-purpose rejection, caller readiness rejection, policy weakening rejection, Sigma predecessor failure propagation, complete global primitive overlay preservation, and continued final-node quarantine.

## Next step

The next semantic surface is Sigma semantic derivations.

A successor Sigma checker should replace V53/V54 registry entries with semantic derivations tied to the executable kernel. It should bind each theorem instance to its formal finite objects, check the corresponding hypergraph or consumer-antichain derivation independently, reject caller-supplied theorem truth assertions, and remain separate from reflection and global-node readiness.
