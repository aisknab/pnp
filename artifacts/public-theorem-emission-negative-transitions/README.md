# Public theorem-emission negative transition artifacts

The public theorem-emission negative transition checker writes its generated verdict here:

```text
artifacts/public-theorem-emission-negative-transitions/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-theorem-emission-negative-transitions0.mjs --json
```

The checker validates that the current preflight and denial surfaces reject premature theorem-emission activation attempts:

```text
release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.json
release/PUBLIC_THEOREM_EMISSION_NEGATIVE_TRANSITIONS.md
PNP_STATUS.json
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json
release/PUBLIC_THEOREM_EMISSION_DENIAL.json
release/RELEASE_BLOCKER_CLEARANCE.json
review/EXTERNAL_REVIEW_STATUS.json
release/PUBLIC_REVIEW_BOUNDARY.json
```

It confirms that the negative transition matrix is rejected and non-activating:

```text
negativeTransitionAuditReady = true
currentDeniedStateAccepted = true
allNegativeTransitionsRejected = true
prematureActivationRejected = true
publicTheoremEmissionAllowedByNegativeTransitions = false
negativeTransitionAuditIsActivationSurface = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
