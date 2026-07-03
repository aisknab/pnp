# Public theorem-emission status artifacts

The public theorem-emission status checker writes its generated verdict here:

```text
artifacts/public-theorem-emission-status/latest-verdict.json
```

The generated verdict is replayed from the current checkout and is not committed as a stable source artifact.

Run it with:

```bash
node pcc-public-theorem-emission-status0.mjs --json
```

The checker validates the current public theorem-emission status summary:

```text
release/PUBLIC_THEOREM_EMISSION_STATUS.json
release/PUBLIC_THEOREM_EMISSION_STATUS.md
PNP_STATUS.json
release/PUBLIC_THEOREM_EMISSION_GATE.json
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json
release/PUBLIC_THEOREM_EMISSION_DENIAL.json
release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json
release/RELEASE_BLOCKER_CLEARANCE.json
review/EXTERNAL_REVIEW_STATUS.json
release/PUBLIC_REVIEW_BOUNDARY.json
```

Current expected generated state:

```text
publicTheoremEmissionStatusReady = true
statusDocReady = true
statusBound = false
gateStatusBound = true
gatePassed = false
gateDenied = true
preflightPassed = false
denialCertificateReady = true
negativeTransitionsRejected = true
releaseBlockersStillActive = true
currentPublicEmissionState = denied
publicTheoremEmissionAllowedByStatus = false
finalTheoremReadyByStatus = false
statusSummaryIsActivationSurface = false
statusSummaryBindingRequiresFuturePR = true
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
