# Public theorem activation gate

Coordinate:

```text
PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01
```

Checker:

```bash
npm run proof:public-theorem-activation
```

Direct checker command:

```bash
node pcc-public-theorem-activation0.mjs --json
```

## Purpose

This gate activates public theorem emission after the proof-only unrestricted final soundness release accepts.

It depends on:

```text
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

## Activation rule

The gate accepts only if the dependency records:

```text
unrestrictedFinalSoundnessDischarged = true
uniformFinalSoundnessProved = true
internalFinalTheoremReady = true
pEqualsNPConclusionAccepted = true
```

and this gate records:

```text
publicTheoremEmissionAllowed = true
publicTheoremStatement = "P = NP"
remainingBlockers = []
```

## External review policy

External review is not a mathematical premise. It remains useful as reproducibility evidence, bug-finding, and independent audit, but it is not required for public theorem emission once the proof stack accepts through UFS-008.

## What this does not claim

This gate does not claim external consensus. It activates the repository's own public theorem emission under its checker trust model.
