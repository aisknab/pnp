# Fresh clone verifier

> **Historical assertion-checker record:** This file documents a superseded checker/release surface.
> It is not current theorem-status authority and does not establish `P = NP`. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

This directory records the historical fresh-clone verification coordinate:

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

Replay the historical full verification path with:

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

## Historical CI smoke mode

The retired GitHub workflow used the same script in a fast smoke mode:

```bash
bash scripts/fresh-clone-verify.sh \
  --repo "$PWD" \
  --ref "$GITHUB_SHA" \
  --verify-command "node --check pcc-core.mjs"
```

That verified the fresh-clone mechanics without recursively running the full `npm run pnp:verify` workflow inside itself. Independent reviewers can use the script default when they want the full historical one-command verifier replay from a clean clone.

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
