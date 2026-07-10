# Release ladder

> **Superseded ledger:** This June 2026 ladder is preserved as historical assertion-checker evidence.
> It is not the current activation policy. Formal reconstruction is in progress, no theorem release
> is active, and the current blockers are listed in
> [`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json). See also
> [`docs/FORMAL_RECONSTRUCTION.md`](./docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-RELEASE-LADDER-2026-06-27-01
```

Machine-readable ledger:

```text
release/RELEASE_LADDER.json
```

Checker:

```bash
node pcc-release-ladder0.mjs --json
```

The historical ladder recorded an ordered checker-release policy. Its external-review blocker model is
superseded. External review remains useful audit evidence but is not a mathematical premise or a
current formal blocker.

## Historical boundary recorded by this ledger

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Historically recorded completed statuses

```text
HistoricalSealedReportExists
PublicReviewBoundaryDeclared
SuccessorReportSealExists
TrustBaseExplicitReady
TrustBaseShrinkPlanReady
OneCommandVerifierReady
MinimalKernelCoordinateReady
MathematicalSemanticsSeedReady
SourceSurfaceHardeningReady
ReproducibilitySeedReady
ReleaseLadderReady
```

## Historically recorded blocked statuses

```text
UnrestrictedFinalSoundnessRepresented
InternalTheoremActivationCandidate
PublicTheoremEmissionCandidate
```

`UnrestrictedFinalSoundnessRepresented` and `InternalTheoremActivationCandidate` remain blocked by:

```text
Release.UnrestrictedFinalSoundness
```

`PublicTheoremEmissionCandidate` remains blocked by:

```text
ExternalReview.Acceptance
```

## Transition rule

A status transition must be explicit, ordered, and machine-checkable. No blocked status may be treated as complete while its blocker is still listed in `remainingBlockers`. Public theorem emission may become available only when the ladder, status file, final theorem readiness, and active final node list all agree.

This ladder is non-activating and subordinate to the formal-reconstruction status. It must not be
used to infer current theorem readiness.
