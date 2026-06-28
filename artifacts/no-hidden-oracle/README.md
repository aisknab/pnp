# No-hidden-oracle artifacts

The audit writes its generated verdict here:

```text
artifacts/no-hidden-oracle/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run audit:no-hidden-oracle
```

The audit validates `oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json` and scans the configured repository source surface for disallowed executable shortcut patterns that would bypass the checked proof-certificate stack.

The accepted verdict is a seed result:

```text
noHiddenOracleAuditReady = true
fullNoHiddenOracleProved = false
```

Formal references are counted but do not authorize executable shortcuts. The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
