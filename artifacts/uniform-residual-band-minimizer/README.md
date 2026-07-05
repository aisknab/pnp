# Uniform residual-band minimizer artifacts

The checker writes its generated verdict here:

```text
artifacts/uniform-residual-band-minimizer/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-residual-band-minimizer
```

or directly with:

```bash
node pcc-uniform-residual-band-minimizer0.mjs --json
```

This artifact surface discharges `UFS-004-ResidualBandMinimizerUniformPolynomial` only. It does not discharge the final SAT-in-P complexity implication, unrestricted final soundness, or final theorem emission.
