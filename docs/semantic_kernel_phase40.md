# Semantic kernel hardening — phase 40

Phase 39 completed bounded semantic coverage of every global final coordinate, but it deliberately left publication separate:

```text
GlobalDAG.SemanticNodeDerivations = ready
Release.PublicTheoremEmission = blocked
```

Phase 40 represents that release/publication boundary explicitly. It does not overwrite the sealed `7072f8d` source/checker release or its sealed artefact release, and it does not activate any public theorem node.

## Public theorem emission gate

The new checker is:

```text
CheckPublicTheoremEmissionGate0
```

It reruns the phase-39 predecessor:

```text
CheckGlobalProofDAGFinalComplexitySuccessor0
```

The predecessor must accept and expose:

```text
globalSemanticNodeDerivationsReady = true
globalFinalDerivationsReady = true
publicTheoremEmissionReady = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
```

All four final theorem coordinates remain quarantined even though their bounded semantic DAG coordinates have been refined.

## Documentation coordinate

The gate binds the immutable documentation coordinate:

```text
PNP-DOC-CPR-2026-06-20-01
```

This coordinate records that source and artefact access instructions are public-repository based and that no access request is required for ordinary review. It also records that the revision is documentation-only and does not overwrite the sealed `7072f8d` source/checker release or sealed artefact bundle.

The documentation patch is:

```text
documentation-revisions/PNP-DOC-CPR-2026-06-20-01/canonical_proof_report.tex.patch
```

The gate binds the documentation-coordinate digest, checker-contract digest, policy digest, and aggregate binding digest.

## Public emission remains blocked

The accepted phase-40 record is a represented blocked release gate, not a public theorem release. It exposes:

```text
publicEmissionGateRepresentedReady = true
publicTheoremEmissionReady = false
publicTheoremEmissionAllowed = false
releasePublicTheoremEmissionBlocked = true
```

The blocker coordinates are:

```text
Release.UnrestrictedFinalSoundness
Documentation.ImmutablePublicRevision
ExternalReview.Acceptance
```

## Successor global gate

The new successor is:

```text
GlobalProofDAGPublicEmissionSuccessor0
```

It preserves the phase-39 semantic overlay and carries the public-emission gate result as a non-DAG release gate. The bounded semantic DAG remains complete:

```text
globalSemanticNodeDerivationsReady = true
globalFinalDerivationsReady = true
```

The public release gate remains closed:

```text
activeFinalNodeIds = []
quarantinedFinalNodeIds = [
  Final.PackageSoundness,
  Final.GeneratedPackageSufficiency,
  Final.AcceptedPackageImpliesSATinP,
  Final.AcceptedPackageImpliesPEqualsNP
]
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

## Verification targets

The dedicated workflow is:

```text
.github/workflows/public-emission-gate.yml
```

It runs:

```text
test/pcc-public-emission-gate0.test.mjs
test/pcc-global-proof-dag-public-emission-successor0.test.mjs
```

## Next step

The next work should address `Release.UnrestrictedFinalSoundness` or construct a new immutable publication coordinate with explicit review status. The sealed report and artefact releases must remain immutable; any public theorem release must be represented as a new coordinate rather than an overwrite.
