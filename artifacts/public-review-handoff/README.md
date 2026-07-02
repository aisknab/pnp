# Public review handoff artifacts

The public review handoff checker writes its generated verdict here:

```text
artifacts/public-review-handoff/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-review-handoff0.mjs --json
```

The checker validates the reviewer-facing entry surface:

```text
release/PUBLIC_REVIEW_HANDOFF.json
release/PUBLIC_REVIEW_HANDOFF.md
release/PUBLIC_REVIEW_BOUNDARY.json
PNP_STATUS.json
```

It confirms that the ordinary one-command verifier and standalone boundary commands are visible while the handoff remains non-activating:

```text
publicReviewHandoffReady = true
handoffDocReady = true
publicReviewBoundaryBound = true
oneCommandVerifierBound = true
directTheoremEmissionAllowedByHandoff = false
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
