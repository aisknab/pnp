# Public theorem activation artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/public-theorem-activation/latest-verdict.json
```

Run it with:

```bash
npm run proof:public-theorem-activation -- --historical-replay
```

or directly with:

```bash
node pcc-public-theorem-activation0.mjs --json --historical-replay
```

This artifact surface historically recorded an activated assertion-checker state. It is withdrawn as
proof authority, does not establish `P = NP`, and cannot change the current formal reconstruction
status.
