# Public theorem-emission denial artifacts

The public theorem-emission denial checker writes its generated verdict here:

```text
artifacts/public-theorem-emission-denial/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-theorem-emission-denial0.mjs --json
```

The checker validates the current denied theorem-emission certificate:

```text
release/PUBLIC_THEOREM_EMISSION_DENIAL.json
release/PUBLIC_THEOREM_EMISSION_DENIAL.md
PNP_STATUS.json
release/PUBLIC_THEOREM_EMISSION_PREFLIGHT.json
release/RELEASE_BLOCKER_CLEARANCE.json
review/EXTERNAL_REVIEW_STATUS.json
release/PUBLIC_REVIEW_BOUNDARY.json
```

It confirms that the public theorem-emission preflight remains denied and that no current surface permits public theorem emission:

```text
denialCertificateReady = true
publicTheoremEmissionDenied = true
publicTheoremEmissionAllowedByDenial = false
publicTheoremEmissionPreflightPassed = false
finalTheoremReadyByDenial = false
blockedByRemainingBlockers = true
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
