# Uniform residual-band minimizer artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/uniform-residual-band-minimizer/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-residual-band-minimizer -- --historical-replay
```

or directly with:

```bash
node pcc-uniform-residual-band-minimizer0.mjs --json --historical-replay
```

This artifact surface discharges `UFS-004-ResidualBandMinimizerUniformPolynomial` only. It does not discharge the final SAT-in-P complexity implication, unrestricted final soundness, or final theorem emission.
