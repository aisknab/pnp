# Semantic kernel hardening — phase 32 (bounded semantic Sigma derivations)

## Purpose

Phase 31 made primitive semantic-rule coverage and K0 semantic conformance ready. The remaining bundle/global blockers were:

```text
Sigma.SemanticDerivations
Reflection.SemanticSoundness
GlobalDAG.SemanticNodeDerivations
```

Phase 32 implements the next semantic surface: bounded finite derivations for the two required Sigma coordinates, V53 and V54.

This phase does not activate final theorem nodes, does not make reflection soundness ready, does not claim an unrestricted universal proof schema beyond the explicitly bounded finite inputs checked by the new executables, and does not modify the sealed `7072f8d` source/checker or artefact release.

## Semantic Sigma checker

The new top-level checker is:

```text
CheckSemanticSigma0
```

It accepts only `SemanticSigmaInput0` records containing:

- a `KImplSemanticFiniteRelSuccessor0` input;
- the legacy K0 conformance suite;
- the accepted semantic K0 conformance suite;
- the legacy Sigma registry;
- a `SemanticSigmaSuite0` containing exact V53 and V54 derivations;
- the fixed fail-closed semantic Sigma policy.

The checker independently requires:

```text
CheckSemanticK0Conformance0 = accept
CheckSigmaRegistry0 = accept
```

before any Sigma readiness is emitted.

Each semantic derivation is bound to:

- the exact legacy Sigma registry-entry digest;
- the exact executable checker-contract digest;
- the exact finite specification;
- the independently computed conclusion;
- a derivation digest over the complete checked record.

Caller fields such as `theoremHolds`, `sound`, `complete`, `classification`, or externally supplied activation results are rejected.

## V53: constant-cut hypergraph rigidity

The executable checker is:

```text
CheckSemanticSigmaV53Derivation0
```

A checked V53 instance supplies:

```text
SemanticSigmaV53Spec0(
  derivationId,
  anchors,
  hyperedges,
  cutValue
)
```

Hyperedges are sparse positive records; omitted hyperedges have implicit weight zero. The checker requires:

- a canonical finite anchor universe;
- canonical unique hyperedge subsets of size at least two;
- bounded nonnegative integer weights;
- a positive bounded proper-cut value;
- exact enumeration of every nonempty proper cut;
- equality of every computed cut sum to the declared cut value.

After checking the premise, the checker independently computes the finite consequence:

- for two anchors, the full pair weight equals the cut value;
- for three anchors, all pair weights are equal and the full-span weight is `D - 2p`;
- for four or more anchors, every proper hyperedge weight is zero and the full-span weight equals `D`.

The mixed three-anchor case is computed explicitly rather than hidden behind a Boolean assertion.

The canonical suite instance is the mixed three-anchor case:

```text
w_ab = w_ac = w_bc = 1
w_abc = 1
D = 3
```

The checker also supports other bounded finite instances and the tests exercise the two-anchor and four-anchor branches.

## V54: consumer-antichain normal form

The executable checker is:

```text
CheckSemanticSigmaV54Derivation0
```

A checked V54 instance supplies:

```text
SemanticSigmaV54Spec0(
  derivationId,
  anchors,
  minimalConsumers
)
```

The minimal-consumer family must be a canonical inclusion antichain. It defines the monotone predicate by upward closure:

```text
r(T) = 1 iff some minimal consumer M is contained in T.
```

The checker enumerates every subset `T` and computes:

```text
kappa(T) = r(T) r(A \ T).
```

It independently verifies:

```text
kappa is nonzero iff the antichain contains a disjoint pair.
```

When every disjoint pair consists of singleton consumers, the checker computes the singleton footprint

```text
E = { a : {a} is a minimal consumer }
```

and verifies on every cut that `kappa` equals the cut indicator of `E`.

The canonical suite instance uses minimal consumers `{a}` and `{b}`. The tests also cover a nonsingleton disjoint-pair case and verify that the checker does not overclaim singleton normal form there.

## Explicit scope boundary

The accepted records state:

```text
boundedFiniteDerivationsOnly = true
unrestrictedUniversalSchemaNotClaimed = true
```

Accordingly, semantic Sigma readiness in this phase means that the repository's required bounded finite Sigma coordinates are represented by executable exact derivation checkers and digest-bound checked instances. It is not a claim that one finite example proves an unrestricted theorem schema for arbitrary unbounded objects.

## KBundle integration

The new successor KBundle is:

```text
KBundleSemanticSigmaSuccessor0
```

It preserves the phase-31 predecessor boundary by rerunning:

```text
CheckKBundleK0ConformanceSuccessor0
```

The predecessor must remain development-only with:

```text
semanticK0ConformanceReady = true
semanticSigmaReady = false
semanticReflectionReady = false
```

The expanded KBundle then runs:

```text
CheckKImplFiniteRelSuccessor0
CheckSemanticSigma0
```

and recomputes the readiness coordinates:

```text
KImpl.SemanticRuleCoverage = ready
K0.SemanticConformance = ready
Sigma.SemanticDerivations = ready
Reflection.SemanticSoundness = blocked
```

The accepted development record remains:

```text
status = development-only
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

An explicit final-purpose KBundle rejects because reflection soundness is still incomplete.

## Global proof-DAG integration

The new successor global gate is:

```text
GlobalProofDAGSemanticSigmaSuccessor0
```

It preserves the phase-31 global predecessor by rerunning:

```text
CheckGlobalProofDAGK0ConformanceSuccessor0
```

The predecessor must remain development-only, expose no active final node, retain complete primitive kernel coverage, and keep Sigma semantic readiness false.

The expanded global overlay activates:

```text
Sigma.V53
Sigma.V54
```

in addition to all sixteen primitive kernel coordinates. Each Sigma global node is bound to:

- its checked derivation digest;
- its conclusion digest;
- its checker-contract digest;
- its legacy registry-entry digest;
- its legacy global-node digest.

The overlay records:

```text
primitiveSemanticRuleCoverageComplete = true
semanticK0ConformanceReady = true
semanticSigmaReady = true
semanticReflectionReady = false
globalSemanticNodeDerivationsReady = false
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
Sigma.SemanticDerivations
```

Remaining blockers:

```text
Reflection.SemanticSoundness
GlobalDAG.SemanticNodeDerivations
```

No public theorem node is activated in this phase.

## Verification targets

The dedicated workflow runs:

```bash
node --test \
  test/pcc-sigma-semantic0.test.mjs \
  test/pcc-kbundle-sigma-successor0.test.mjs \
  test/pcc-global-proof-dag-sigma-successor0.test.mjs
```

The tests cover:

- V53 two-anchor, mixed three-anchor, and four-anchor full-span cases;
- exact proper-cut enumeration;
- nonconstant-cut rejection;
- caller theorem-truth rejection;
- V54 singleton normal form;
- V54 nonsingleton disjoint-pair behavior without overclaim;
- non-antichain rejection;
- registry-entry digest binding;
- missing V54 rejection;
- K0-conformance predecessor preservation;
- KBundle readiness recomputation;
- global Sigma-node digest binding;
- continued final-node quarantine.

## Next step

The next semantic surface is reflection soundness.

A successor reflection checker should replace registry mappings with proof-producing refinement records. Each reflected checker coordinate must be bound to the executable checker contract, accepted/rejected normal forms, public conclusion, and a checked simulation or refinement argument. Caller-supplied `sound = true` fields must remain forbidden, and global final-node quarantine must remain active until reflection and the remaining global theorem nodes are semantically derived.
