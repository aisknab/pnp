# Unrestricted final soundness release transition

Coordinate:

```text
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

Uniform final soundness obligation:

```text
UFS-008-ReleaseTransitionFromProofOnly
```

Checker:

```bash
npm run proof:unrestricted-final-soundness-release
```

Direct checker command:

```bash
node pcc-unrestricted-final-soundness-release0.mjs --json
```

## Purpose

This surface discharges the eighth uniform-final-soundness sub-obligation: clear `Release.UnrestrictedFinalSoundness` from accepted proof objects only.

The release transition requires:

```text
UFS-001 through UFS-007 all accept
accepted dependency outputs are hash-bound
UFS-007 accepts SAT in P and P = NP as the complexity conclusion
external review is not used as a mathematical premise
historical report prose is not used as a mathematical premise
public-site wording is not used as a mathematical premise
```

## What this clears

This checker clears:

```text
Release.UnrestrictedFinalSoundness
```

and records:

```text
unrestrictedFinalSoundnessDischarged = true
uniformFinalSoundnessProved = true
internalFinalTheoremReady = true
```

## What this does not clear

This checker does not itself activate public theorem emission. It leaves the public/review publication policy as an explicit later gate:

```text
publicTheoremEmissionAllowed = false
remainingBlockers = [
  "ExternalReview.Acceptance"
]
```

The point is to separate mathematical proof readiness from communication/release policy.

## Required proof obligations

```text
REL-001-AllUFSDependenciesAccepted
REL-002-DependencyVerdictsHashBound
REL-003-ComplexityConclusionBound
REL-004-NoExternalReviewPremise
REL-005-ClearUnrestrictedFinalSoundnessOnly
REL-006-NoPrematurePublicTheoremEmission
```

## Next step

After this checker accepts, the remaining work is an explicit public theorem activation policy gate. That gate may decide whether external review remains a publication blocker, but it cannot be a mathematical premise for the proof.
