# Complexity ledger artifacts

The complexity ledger checker writes its generated verdict here:

```text
artifacts/complexity-ledger/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run complexity:ledger
```

The checker validates `complexity/COMPLEXITY_LEDGER.json`, verifies the fixed proof-object chain, checks premise ordering, validates evidence-file existence, rejects activated derived conclusions, and preserves the public-review boundary.

The accepted verdict is a seed implication ledger, not a full theorem activation:

```text
complexityLedgerReady = true
fullComplexityImplicationDischarged = false
publicTheoremEmissionAllowedByLedger = false
```

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
