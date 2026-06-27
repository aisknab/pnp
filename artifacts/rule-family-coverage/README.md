# Rule-family coverage artifacts

The rule-family coverage checker writes its latest generated verdict here:

```text
artifacts/rule-family-coverage/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run rule-family:coverage
```

The checker validates `semantic-kernel/RULE_FAMILY_COVERAGE.json`, verifies the fixed seed family set, checks positive, negative, and mutation counts, validates evidence files, and preserves the public-review boundary.

The accepted verdict is a seed ledger, not a full historical coverage claim:

```text
coverageLedgerReady = true
fullRuleFamilyCoverageProved = false
```

Future PRs should expand the ledger until every relevant rule family, checker family, and theorem-binding family has complete positive, negative, and mutation coverage.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
