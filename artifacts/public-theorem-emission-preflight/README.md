# Public theorem emission preflight artifacts

The public theorem emission preflight checker writes its generated verdict here:

```text
artifacts/public-theorem-emission-preflight/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-theorem-emission-preflight0.mjs --json
```

The checker validates the current theorem-emission-denied state:

```text
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.md
PNP_STATUS.json
release/PUBLIC_REVIEW_BOUNDARY.json
release/RELEASE_BLOCKER_CLEARANCE.json
review/EXTERNAL_REVIEW_STATUS.json
release/RELEASE_LADDER.json
proof-obligations/GAP_LEDGER.json
proof-obligations/OBLIGATION_LEDGER.json
```

It confirms that the preflight is ready but intentionally does not pass in the current state:

```text
publicTheoremEmissionPreflightReady = true
publicTheoremEmissionPreflightPassed = false
publicTheoremEmissionDenied = true
finalTheoremReadyByPreflight = false
releaseBlockerClearanceAccepted = false
externalReviewAcceptanceClaimed = false
unrestrictedFinalSoundnessClearanceAccepted = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
