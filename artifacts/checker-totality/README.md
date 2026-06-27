# Checker totality artifacts

The checker-totality audit writes its latest generated verdict here:

```text
artifacts/checker-totality/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run checker:totality
```

The audit currently inventories every exported `Check*0` function found in repository `.mjs` files, then fuzzes the public self-verification checker surface listed in `checker-totality/CHECKER_TOTALITY_AUDIT.json`.

The accepted verdict is a seed result:

```text
checkerTotalitySeedReady = true
fullCheckerTotalityProved = false
```

That means the audit is active and executable, but it does not yet claim every historical checker has been fuzzed for totality. Future PRs should move audited checkers from the unaudited inventory into the required fuzz surface until the full exported inventory is covered.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
