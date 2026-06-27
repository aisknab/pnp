# Trust-base artifacts

The trust-base checker writes its latest generated verdict here:

```text
artifacts/trust-base/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-trust-base0.mjs --json
```

The checker validates `trust-base/TRUST_BASE.json`, verifies `trust-base/SHA256SUMS`, checks that every required trust-base assumption is present and non-empty, verifies the represented files exist, and preserves the public-review boundary.

The trust base is explicit, not empty:

```text
trustBaseRepresentedReady = true
trustBaseExplicit = true
trustBaseEmpty = false
```

The trust-base verdict does not clear the remaining blockers and does not activate public theorem emission.
