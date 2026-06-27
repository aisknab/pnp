# Negative checker mutation seed suite

This directory defines the current negative-checker mutation coordinate:

```text
PNP-NEGATIVE-CHECKER-MUTATIONS-2026-06-27-01
```

The machine-readable manifest is:

```text
checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json
```

The audit runs valid baselines plus targeted negative mutations for the current public self-verification checker surface. Every mutation must return `reject`; throwing or accepting is a failure.

The seed suite is intentionally not a full-coverage claim:

```text
negativeMutationSeedReady = true
fullNegativeMutationCoverageProved = false
```

Run it with:

```bash
npm run checker:mutations
```

The current seed covers mutation families such as kind mismatch, public-boundary activation, missing dependencies, caller-supplied readiness, checksum mismatch, premature completion, and public-surface drift.

The audit preserves the public-review boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
