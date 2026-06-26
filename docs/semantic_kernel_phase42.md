# Semantic kernel hardening - phase 42

Phase 41 added the public-review documentation coordinate:

```text
PNP-DOC-CPR-2026-06-26-01
```

Phase 42 binds that coordinate into a new publication-coordinate gate. This is the step that discharges the represented documentation blocker without opening public theorem emission.

## New checker

```text
CheckPublicationCoordinateGate0
```

The checker requires the phase-40 public-emission predecessor:

```text
CheckGlobalProofDAGPublicEmissionSuccessor0 = accept
```

The predecessor must still expose the old blocker set:

```text
Release.UnrestrictedFinalSoundness
Documentation.ImmutablePublicRevision
ExternalReview.Acceptance
```

## Bound documentation coordinate

The checker requires exactly:

```text
PNP-DOC-CPR-2026-06-26-01
```

with the recorded revised payload hashes:

```text
9ad7ed91a48662b98432e2b6000beaf06b3ebd2212de3a6d820a7dcbd27e8d9a  canonical_proof_report.tex
f6848d37eb8982f59ca1436352e06559e35aad8ee56956705de2650de1cc45a7  canonical_proof_report.pdf
effbcf2e20436535248b39e59170538422abd4348de7b8dbf43035118609367a  canonical_proof_report.tex.patch
```

The coordinate states:

```text
sealedReleaseNotOverwritten = true
documentationOnlyRevision = true
publicReviewPublicationFraming = true
sourceAndArtifactAccessPublicWithoutRequest = true
publicTheoremEmissionNotActivated = true
```

## Discharged blocker

Phase 42 discharges only:

```text
Documentation.ImmutablePublicRevision
```

## Remaining blockers

Publication remains blocked on:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

The checker keeps:

```text
publicTheoremEmissionReady = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
```

## Verification

The dedicated workflow is:

```text
.github/workflows/publication-coordinate-gate.yml
```

It runs:

```bash
node --check pcc-publication-coordinate-gate0.mjs
node --test test/pcc-publication-coordinate-gate0.test.mjs
```

## Next step

The next release-layer work should represent either unrestricted final-soundness review status or external-review acceptance. Those must remain separate coordinates; this phase does not make a public theorem claim and does not modify the sealed release.