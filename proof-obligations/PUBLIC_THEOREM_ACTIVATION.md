# Public theorem activation gate

> **Withdrawn activation:** This coordinate is superseded and is not current theorem authority.
> The repository does not currently establish `P = NP`, and public theorem emission is disabled.
> See [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json)
> and [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01
```

Historical replay command:

```bash
npm run proof:public-theorem-activation -- --historical-replay
```

Direct historical replay command:

```bash
node pcc-public-theorem-activation0.mjs --json --historical-replay
```

## Historical purpose

This gate recorded the old JavaScript assertion stack's activation decision after its unrestricted
final-soundness record accepted. That transition did not establish the named mathematical claims.

It depends on:

```text
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

## Historical activation rule

The historical gate accepted only if the dependency recorded:

```text
unrestrictedFinalSoundnessDischarged = true
uniformFinalSoundnessProved = true
internalFinalTheoremReady = true
pEqualsNPConclusionAccepted = true
```

and the activation record asserted:

```text
publicTheoremEmissionAllowed = true
publicTheoremStatement = "P = NP"
remainingBlockers = []
```

## External review policy

External review is not a mathematical premise. It remains useful for reproduction, bug finding, and
independent audit. Current activation depends only on the concrete formal conditions in the
formal-reconstruction notice, not on acceptance of UFS assertion records.

## Evidence boundary

Replaying this gate shows what the historical checker accepted. It does not activate current public
theorem emission, establish `P = NP`, or supply a formal derivation of any UFS proposition.
