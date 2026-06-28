# Multi-platform core CI

This directory records the current multi-platform CI coordinate:

```text
PNP-MULTI-PLATFORM-CI-2026-06-27-01
```

The machine-readable manifest is:

```text
reproducibility/MULTI_PLATFORM_CI.json
```

The workflow is:

```text
.github/workflows/multi-platform-ci.yml
```

It runs on:

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

This workflow is a cross-platform reproducibility confidence layer for the Node core. It deliberately does not run Docker, execute the bash fresh-clone verifier, or recursively run the full `npm run pnp:verify` command on every hosted operating system.

The full verifier remains:

```bash
npm run pnp:verify
```

The multi-platform workflow proves that the lockfile install, core syntax, one-command verifier script syntax, manifest checks, and reviewer negative invariants run on Ubuntu, macOS, and Windows.

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
