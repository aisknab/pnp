# Public surface baseline artifacts

The public surface baseline checker writes its generated verdict here:

```text
artifacts/public-surface-baseline/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-public-surface-baseline0.mjs --json
```

The checker validates:

```text
pcc-public-surface-freeze0.mjs
index.mjs
package.json
PNP_STATUS.json
```

It confirms that the package public entry surface, package exports, package bins, and package scripts match the public-review baseline:

```text
PUBLIC-SURFACE-BASELINE-2026-06-27-NO-HIDDEN-ORACLE-01
```

The checker is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
