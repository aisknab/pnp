# Cross-verifier artifacts

`scripts/cross-verify.mjs` writes the latest cross-runtime minimal-kernel agreement verdict to `artifacts/cross-verify/latest-verdict.json`.

The generated verdict is intentionally not committed as a stable source artifact. It is a replay product of the current checkout.

Run it with `npm run cross-verify:json`.

The command runs the JavaScript minimal-kernel checker, the JavaScript theorem-binding ledger audit, and the independent Python minimal-kernel verifier. It accepts only when they agree on the minimal-kernel coordinate, byte SHA256 values for the kernel and binding ledgers, checker-surface count, proof-spine count, the disabled public-emission state, the disabled final-readiness state, empty active final nodes, and the blocker list.

The package script surface is intentionally rebaselined for the public-review self-verification track. `cross-verify` and `cross-verify:json` are now first-class package scripts, and `CheckPublicEntryReleaseSurface0` records the baseline coordinate for that change.

The cross-verifier verdict is a redundancy and reproducibility check only. It does not clear the remaining blockers and does not activate public emission.
