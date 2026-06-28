# Fresh clone verifier

This directory records the current fresh-clone verification coordinate:

```text
PNP-FRESH-CLONE-VERIFY-2026-06-27-01
```

The machine-readable manifest is:

```text
reproducibility/FRESH_CLONE_VERIFY.json
```

The executable entrypoint is:

```text
scripts/fresh-clone-verify.sh
```

Run the default full verification path with:

```bash
bash scripts/fresh-clone-verify.sh \
  --repo https://github.com/aisknab/pnp.git \
  --ref main
```

By default, the script performs:

```text
git clone <repo> <workdir>/repo
git checkout --detach <ref>
npm ci
npm run pnp:verify
```

The script writes a generated verdict to:

```text
artifacts/fresh-clone-verify/latest-verdict.json
```

## CI smoke mode

The GitHub workflow uses the same script in a fast smoke mode:

```bash
bash scripts/fresh-clone-verify.sh \
  --repo "$PWD" \
  --ref "$GITHUB_SHA" \
  --verify-command "node --check pcc-core.mjs"
```

That verifies the fresh-clone mechanics without recursively running the full `npm run pnp:verify` workflow inside itself. Independent reviewers should use the script default when they want the full one-command verifier replay from a clean clone.

## Boundary

The fresh-clone verifier is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
