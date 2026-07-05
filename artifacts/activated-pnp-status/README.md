# Activated PNP status artifacts

The checker writes its generated verdict here:

```text
artifacts/activated-pnp-status/latest-verdict.json
```

Run it with:

```bash
npm run proof:activated-pnp-status
```

or directly with:

```bash
node pcc-activated-pnp-status0.mjs --json
```

This artifact surface verifies that `status/ACTIVATED_PNP_STATUS.json` and `public/pnp-status.json` mirror the accepted public theorem activation state. It leaves the older `PNP_STATUS.json` public-review payload in place as a legacy boundary surface for the older public-review checks.
