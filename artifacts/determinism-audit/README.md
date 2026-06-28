# Determinism audit artifacts

The determinism audit writes its generated verdict here:

```text
artifacts/determinism-audit/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run the stronger default replay with:

```bash
node scripts/audit-determinism.mjs --json
```

The default command runs a reduced one-command verifier twice:

```bash
node scripts/pnp-verify-all.mjs --json --skip-unit-tests --skip-release-audit
```

The CI smoke workflow uses a faster deterministic checker:

```bash
node scripts/audit-determinism.mjs \
  --json \
  --command "node pcc-complexity-ledger0.mjs --json" \
  --generated-artifact artifacts/complexity-ledger/latest-verdict.json
```

The audit compares command output, parsed JSON canonical digests when available, stable source artifact hashes, and generated verdict artifact hashes.

The determinism audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
