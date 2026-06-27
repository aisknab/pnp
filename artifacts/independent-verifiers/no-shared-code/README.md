# Independent verifier no-shared-code artifacts

The no-shared-code audit writes its latest generated verdict here:

```text
artifacts/independent-verifiers/no-shared-code/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run independent:no-shared-code
```

The audit validates `independent-verifiers/NO_SHARED_CODE_POLICY.json`, scans the independent verifier source tree, and rejects forbidden imports, dynamic execution patterns, unsupported file types, symlinks, and policy changes that would allow shared JavaScript checker code.

The audit is a redundancy-strengthening layer only. It does not clear the remaining blockers and does not activate public theorem emission.
