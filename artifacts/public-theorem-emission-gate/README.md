# Public theorem-emission gate artifacts

The public theorem-emission gate checker writes its generated verdict here:

```text
artifacts/public-theorem-emission-gate/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-theorem-emission-gate0.mjs --json
```

The checker validates the current denied theorem-emission gate:

```text
release/PUBLIC_THEOREM_EMISSION_GATE.json
release/PUBLIC_THEOREM_EMISSION_GATE.md
PNP_STATUS.json
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json
release/PUBLIC_THEOREM_EMISSION_DENIAL.json
release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json
release/RELEASE_BLOCKER_CLEARANCE.json
review/EXTERNAL_REVIEW_STATUS.json
release/PUBLIC_REVIEW_BOUNDARY.json
```

It confirms that the current gate is ready, denied, negative-transition-covered, and non-activating:

```text
publicTheoremEmissionGateReady = true
publicTheoremEmissionGatePassed = false
publicTheoremEmissionDenied = true
allNegativeTransitionsRejected = true
prematureActivationRejected = true
publicTheoremEmissionAllowedByGate = false
finalTheoremReadyByGate = false
gateIsActivationSurface = false
gateBindingRequiresFuturePR = true
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
