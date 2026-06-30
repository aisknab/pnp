# PNP verify-all artifact

The one-command verifier writes its latest generated verdict here:

```text
artifacts/pnp-verify-all/latest-verdict.json
```

Run it with:

```bash
npm run pnp:verify
```

Current direct-binding seed audits include Base, CHG, Mode, E, N, FT, X, BC, UN, HN, HResolve, BUD, and NOR/FF.

```text
NOR/FF -> pcc-direct-bind-frontier-faithful0.mjs
```

The accepted verdict keeps the public-review boundary explicit:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
