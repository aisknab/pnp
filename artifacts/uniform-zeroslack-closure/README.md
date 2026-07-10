# Uniform ZeroSlack closure artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/uniform-zeroslack-closure/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-zeroslack-closure -- --historical-replay
```

or directly with:

```bash
node pcc-uniform-zeroslack-closure0.mjs --json --historical-replay
```

This artifact surface discharges `UFS-005-ZeroSlackContradictionUniform` only. It does not discharge the final complexity implication, unrestricted final soundness, or final theorem emission.
