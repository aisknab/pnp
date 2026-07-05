# Public theorem activation artifacts

The checker writes its generated verdict here:

```text
artifacts/public-theorem-activation/latest-verdict.json
```

Run it with:

```bash
npm run proof:public-theorem-activation
```

or directly with:

```bash
node pcc-public-theorem-activation0.mjs --json
```

This artifact surface activates public theorem emission under the repository checker trust model after unrestricted final soundness has been discharged. It does not claim independent external consensus and does not mutate the historical sealed report.
