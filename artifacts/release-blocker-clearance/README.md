# Release blocker clearance artifacts

The release blocker clearance checker writes its generated verdict here:

```text
artifacts/release-blocker-clearance/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-release-blocker-clearance0.mjs --json
```

The checker validates the current non-clearing release-blocker protocol:

```text
release/RELEASE_BLOCKER_CLEARANCE.json
release/RELEASE_BLOCKER_CLEARANCE.md
PNP_STATUS.json
release/RELEASE_LADDER.json
proof-obligations/GAP_LEDGER.json
proof-obligations/OBLIGATION_LEDGER.json
review/EXTERNAL_REVIEW_STATUS.json
review/PUBLIC_REVIEW_CHECKLIST.json
```

It confirms that both release blockers remain active and that no current checker permits public theorem emission:

```text
clearanceProtocolReady = true
releaseBlockersStillActive = true
releaseBlockerClearanceAccepted = false
unrestrictedFinalSoundnessClearanceAccepted = false
externalReviewClearanceAccepted = false
publicTheoremEmissionAllowedByClearance = false
finalTheoremReadyByClearance = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
