# Fresh clone verifier artifacts

The fresh clone verifier writes its generated verdict here:

```text
artifacts/fresh-clone-verify/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout or by an independent reviewer from a fresh clone.

Run the default full verification path with:

```bash
bash scripts/fresh-clone-verify.sh \
  --repo https://github.com/aisknab/pnp.git \
  --ref main
```

By default, the script clones the repository, checks out the requested ref, runs `npm ci`, and then runs `npm run pnp:verify`.

The CI workflow uses the same script with a smoke verification command so it does not recursively execute the full verifier inside the fresh clone:

```bash
bash scripts/fresh-clone-verify.sh \
  --repo "$PWD" \
  --ref "$GITHUB_SHA" \
  --verify-command "node --check pcc-core.mjs"
```

The verifier is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
