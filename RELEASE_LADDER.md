# Release ladder

Current coordinate:

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

The project does not jump from accepted package evidence to public theorem emission. It passes through explicit, ordered release gates. The current ladder records completed public-review infrastructure and keeps final theorem activation blocked until unrestricted final soundness and external review acceptance are represented as cleared release states.

## Current boundary

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Current completed statuses

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

## Current blocked statuses

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

This ladder is non-activating. It records the path from public-review evidence toward theorem-emission eligibility but does not clear the current blockers.
