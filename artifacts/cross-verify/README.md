# Cross-verifier artifacts

`scripts/cross-verify.mjs` writes the latest cross-runtime minimal-kernel agreement verdict here:

```text
artifacts/cross-verify/latest-verdict.json
```

The generated verdict is intentionally not committed as a stable source artifact. It is a replay product of the current checkout.

## Command

```bash
npm run cross-verify:json
```

The command runs three agreement surfaces:

1. JavaScript minimal-kernel checker: `CheckMinimalKernel0`.
2. JavaScript theorem-binding ledger audit: `scripts/audit-report-theorem-bindings.mjs`.
3. Independent Python minimal-kernel verifier: `independent-verifiers/python/verify_minimal_kernel.py`.

The verdict accepts only if the verifiers agree on:

- the minimal-kernel coordinate,
- the byte SHA256 of `kernel/PNP_MINIMAL_KERNEL.json`,
- the byte SHA256 of `report-bindings/REPORT_THEOREM_BINDINGS.json`,
- checker-surface count,
- proof-spine count,
- disabled public theorem emission,
- disabled final-theorem readiness,
- empty active final nodes, and
- exact remaining blockers.

## Boundary

The cross-verifier verdict is a redundancy and reproducibility check. It does not discharge `Release.UnrestrictedFinalSoundness`, does not discharge `ExternalReview.Acceptance`, and does not allow public theorem emission.
