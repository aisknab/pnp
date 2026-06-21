# Semantic kernel hardening — phase 6 (successor KBundle and global gate)

## Purpose

Phases 1–5 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, and fail-closed successor KImpl boundaries.

Phase 6 carries those computed results into two wider architectural boundaries:

1. a successor KBundle that distinguishes legacy structural acceptance from semantic readiness;
2. a successor global proof-DAG gate that quarantines legacy final theorem nodes until the computed semantic chain is complete.

This phase does not modify or reinterpret the sealed `7072f8d` source/checker or artefact release.

## Why a successor boundary is required

The legacy KBundle runs four surfaces:

```text
CheckKImpl0
CheckConformance0
CheckSigmaRegistry0
CheckReflectionRegistry0
```

Those checks remain useful for structure, coverage, canonical records, and linkage. They do not by themselves establish:

- semantic soundness of every primitive rule;
- semantic conformance of the primitive-rule test suite;
- derivations of V53 and V54;
- proof-producing refinement from executable checker acceptance to public mathematical conclusions.

Likewise, the legacy global proof DAG checks node kinds, topological references, required coordinates, mode and bounds firewalls, imports, no-hidden-minimization constraints, and node digests. Its own reviewer boundary states that it does not prove the semantic implication represented by a correctly linked node.

A structurally accepted legacy final node must therefore not become active merely because it is present and linked.

## Successor KBundle

`KBundleSemanticSuccessor0` contains:

```text
Purpose                  development | final-theorem
SemanticKImpl             development-purpose KImplSemanticDAGIndSuccessor0
K0                        legacy conformance suite
PSigma                    legacy Sigma registry
ReflectionRegistry        legacy reflection registry
Binding                   fixed executable checker binding
Policy                    fixed fail-closed release policy
```

The nested semantic KImpl input is required to remain development-purpose. Final KImpl readiness is recomputed internally by constructing a final-purpose probe and calling:

```text
CheckKImplDAGIndFinalTheoremReadiness0
```

The caller cannot provide a final-ready child record, readiness booleans, a missing-rule override, or a weakened policy.

### Development checking

`CheckKBundleSemanticSuccessor0` requires:

1. accepted development `CheckKImplDAGIndSuccessor0`;
2. preserved `development-only` KImpl status;
3. accepted legacy `CheckKBundle0` over the same base KImpl, K0, Sigma, and reflection records;
4. a computed final KImpl probe;
5. a computed four-surface readiness record.

A development result records the current boundaries explicitly:

```text
legacy conformance      structural-only
legacy Sigma            registry-shape-only
legacy reflection       mapping-shape-only
semantic conformance    not ready
semantic Sigma          not ready
semantic reflection     not ready
```

### Computed readiness record

The checker emits `KBundleComputedSemanticReadiness0` with four coordinates:

```text
KImpl.SemanticRuleCoverage
K0.SemanticConformance
Sigma.SemanticDerivations
Reflection.SemanticSoundness
```

The first coordinate is tied to the digest of the independently executed final KImpl probe. The other three remain blocked because no semantic successor checkers for those surfaces exist yet.

`CheckKBundleSemanticFinalTheoremReadiness0` rejects unless all four coordinates are ready.

## Successor global proof DAG

`GlobalProofDAGSemanticSuccessor0` contains:

```text
Purpose                  development | final-theorem
KBundle                   development-purpose KBundleSemanticSuccessor0
LegacyGlobalProofDAG      GlobalProofDAG0
Binding                   fixed executable checker binding
Policy                    fixed final-node quarantine policy
```

The nested KBundle is also required to remain development-purpose. Final bundle readiness is recomputed internally through:

```text
CheckKBundleSemanticFinalTheoremReadiness0
```

The legacy graph is still validated by `CheckGlobalProofDAG0`. Its accepted result is classified as `structural-only`.

## Semantic overlay

The successor checker computes a semantic overlay over the legacy coordinates.

At this phase, the semantically implemented kernel coordinates are:

```text
K.Eq
K.Subst
K.Record
K.DAGInd
```

The remaining twelve kernel coordinates are present structurally but blocked semantically. Every non-kernel legacy node — including Sigma, reflection, row, package, and final nodes — is classified as structural-only until migrated to a semantic derivation.

The overlay requires a legacy `K.<rule>` coordinate for every rule in the semantic required-rule universe. It also requires the four legacy final coordinates as quarantined nodes:

```text
Final.PackageSoundness
Final.GeneratedPackageSufficiency
Final.AcceptedPackageImpliesSATinP
Final.AcceptedPackageImpliesPEqualsNP
```

## Computed global gate

The checker emits a small derived gate DAG:

```text
Gate.KBundle.DevelopmentAcceptance
Gate.KBundle.FinalReadiness
Gate.GlobalDAG.StructuralAcceptance
Gate.GlobalDAG.SemanticNodeDerivations
Gate.FinalTheorem.Readiness
```

The final gate depends on both:

```text
Gate.KBundle.FinalReadiness
Gate.GlobalDAG.SemanticNodeDerivations
```

The KBundle gate is tied to the computed KBundle final-probe digest. The global semantic-node gate remains false because the legacy Sigma, reflection, package, and final theorem nodes have not yet been re-encoded as semantic derivations.

Consequently, a development result is forced to record:

```text
status = development-only
legacyGlobalDAGSemanticStatus = structural-only
legacyFinalNodesQuarantined = true
activeFinalNodeIds = []
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

`CheckGlobalProofDAGSemanticFinalTheoremReadiness0` rejects until the computed gate accepts. Caller-supplied active-final lists or readiness flags are forbidden.

## Current readiness result

The executable primitive rule families are:

```text
Eq
Subst
Record
DAGInd
```

Twelve primitive rules remain missing:

```text
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

In addition, semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations remain blocked.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kbundle-semantic-successor0.test.mjs \
  test/pcc-global-proof-dag-semantic-successor0.test.mjs
```

The tests cover:

- development-only KBundle acceptance;
- exact KBundle blocker coordinates;
- final-purpose and explicit final-gate rejection;
- caller readiness and policy-weakening rejection;
- propagation of semantic KImpl and legacy Sigma failures;
- development-only global successor acceptance;
- exact quarantine of all four legacy final nodes;
- exact semantic overlay of implemented and blocked kernel coordinates;
- computed global gate dependencies;
- binding of the global gate to the computed KBundle readiness digest;
- propagation of successor KBundle and legacy global-DAG failures.

## Next step

After this phase is accepted, the next soundness step is to implement the `LedgerInd` primitive. The successor KBundle and global gate should then consume the expanded semantic KImpl record without changing their fail-closed policies. Sigma, reflection, package, and final-node migration remains a separate required sequence; structural legacy acceptance never substitutes for those semantic derivations.
