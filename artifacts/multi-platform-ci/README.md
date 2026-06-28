# Multi-platform CI artifacts

The multi-platform CI workflow does not commit generated runtime artifacts. It validates the source manifest and runs a portable Node core subset on Ubuntu, macOS, and Windows.

The source coordinate is:

```text
PNP-MULTI-PLATFORM-CI-2026-06-27-01
```

The workflow runs:

```bash
npm ci
node --check pcc-core.mjs
node --check scripts/pnp-verify-all.mjs
node --test audits/multi-platform-ci0.test.mjs
node --test test/reviewer-negative-invariants.test.mjs
```

This is a reproducibility confidence layer for the portable Node core. It does not replace `npm run pnp:verify`, and it does not clear the remaining blockers or allow public theorem emission.
