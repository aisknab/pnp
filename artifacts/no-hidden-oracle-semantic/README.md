# Semantic no-hidden-oracle artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/no-hidden-oracle-semantic/latest-verdict.json
```

Run it with:

```bash
npm run proof:no-hidden-oracle-semantic -- --historical-replay
```

or directly with:

```bash
node pcc-no-hidden-oracle-semantic0.mjs --json --historical-replay
```

This artifact surface discharges `UFS-006-NoHiddenOracleSemanticCompleteness` only. It does not discharge the final complexity implication, unrestricted final soundness, or final theorem emission.
