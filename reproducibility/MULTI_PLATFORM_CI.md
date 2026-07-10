# Multi-platform core CI

> Historical assertion-checker record. Its workflow is retired and it is not current theorem-status authority. See [the formal reconstruction status](../status/FORMAL_RECONSTRUCTION_STATUS.json).

This directory preserves the retired multi-platform CI coordinate:

```text
PNP-MULTI-PLATFORM-CI-2026-06-27-01
```

The machine-readable manifest is:

```text
reproducibility/MULTI_PLATFORM_CI.json
```

The historical workflow path was:

```text
retired historical workflow `multi-platform-ci.yml`
```

The retired matrix ran on:

```text
ubuntu-latest
macos-latest
windows-latest
```

The portable core command set is:

```bash
npm ci
node --check pcc-core.mjs
node --check scripts/pnp-verify-all.mjs
node --test audits/multi-platform-ci0.test.mjs
node --test test/reviewer-negative-invariants.test.mjs
```

## Scope

This retired workflow was a cross-platform reproducibility confidence layer for the Node core. It deliberately did not run Docker, execute the bash fresh-clone verifier, or recursively run the full `npm run pnp:verify` command on every hosted operating system.

The full verifier remains:

```bash
npm run pnp:verify
```

The record preserves what the retired workflow checked. It makes no claim about the current checkout or current hosted runners.

## Boundary

The multi-platform CI surface is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

It does not yet claim full bit-identical behavior across every operating system.
