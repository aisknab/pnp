# Semantic no-hidden-oracle artifacts

The checker writes its generated verdict here:

```text
artifacts/no-hidden-oracle-semantic/latest-verdict.json
```

Run it with:

```bash
npm run proof:no-hidden-oracle-semantic
```

or directly with:

```bash
node pcc-no-hidden-oracle-semantic0.mjs --json
```

This artifact surface discharges `UFS-006-NoHiddenOracleSemanticCompleteness` only. It does not discharge the final complexity implication, unrestricted final soundness, or final theorem emission.
