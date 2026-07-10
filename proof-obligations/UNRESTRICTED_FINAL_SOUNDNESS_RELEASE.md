# Unrestricted final soundness release transition

> **Withdrawn release transition:** This coordinate is superseded. Its assertion-checker acceptance
> does not discharge unrestricted final soundness or make an internal theorem ready. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-008-ReleaseTransitionFromProofOnly
```

Historical replay command:

```bash
npm run proof:unrestricted-final-soundness-release -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-unrestricted-final-soundness-release0.mjs --json --historical-replay
```

## Purpose

This surface recorded the eighth historical UFS transition. It cleared a JavaScript release-policy
field after UFS assertion records accepted; it did not prove unrestricted final soundness.

The release transition requires:

```text
UFS-001 through UFS-007 all accept
accepted dependency outputs are hash-bound
UFS-007 accepts SAT in P and P = NP as the complexity conclusion
external review is not used as a mathematical premise
historical report prose is not used as a mathematical premise
public-site wording is not used as a mathematical premise
```

## What the historical record asserted

The historical checker cleared the field:

```text
Release.UnrestrictedFinalSoundness
```

and records:

```text
unrestrictedFinalSoundnessDischarged = true
uniformFinalSoundnessProved = true
internalFinalTheoremReady = true
```

## Current effect

The historical record left public emission to a later gate:

```text
publicTheoremEmissionAllowed = false
remainingBlockers = [
  "ExternalReview.Acceptance"
]
```

Neither historical field transition has current effect. Current status keeps unrestricted final
soundness, uniform final soundness, and internal theorem readiness false.

## Required proof obligations

```text
REL-001-AllUFSDependenciesAccepted
REL-002-DependencyVerdictsHashBound
REL-003-ComplexityConclusionBound
REL-004-NoExternalReviewPremise
REL-005-ClearUnrestrictedFinalSoundnessOnly
REL-006-NoPrematurePublicTheoremEmission
```

## Historical next step

The old next step was the now-withdrawn public-theorem activation gate. Future activation instead
requires the concrete, assumption-audited Lean conditions in the formal-reconstruction notice.
