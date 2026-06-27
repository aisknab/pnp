# Negative checker mutation artifacts

The negative checker mutation audit writes its latest generated verdict here:

```text
artifacts/checker-mutations/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run checker:mutations
```

The audit validates `checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json`, runs valid baselines for the public self-verification checker seed set, then applies targeted mutations that must return `reject` without throwing.

The accepted verdict is a seed result:

```text
negativeMutationSeedReady = true
fullNegativeMutationCoverageProved = false
```

Future PRs should expand the generated mutation corpus until every checker family has positive and negative mutation coverage.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
