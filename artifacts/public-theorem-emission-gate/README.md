# Public theorem gate artifacts

The checker writes its generated verdict here:

```text
artifacts/public-theorem-emission-gate/latest-verdict.json
```

The generated verdict is replayed from the current checkout and is not committed as a stable source artifact.

Run it with:

```bash
node pcc-public-theorem-emission-gate0.mjs --json
```

Current expected generated state:

```text
publicTheoremEmissionGateReady = true
publicTheoremEmissionGatePassed = false
publicTheoremEmissionDenied = true
statusBound = true
allNegativeTransitionsRejected = true
prematureActivationRejected = true
publicTheoremEmissionAllowedByGate = false
finalTheoremReadyByGate = false
gateIsActivationSurface = false
gateBindingRequiresFuturePR = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
