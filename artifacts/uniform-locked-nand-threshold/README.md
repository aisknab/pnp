# Uniform locked NAND threshold artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/uniform-locked-nand-threshold/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-locked-nand-threshold -- --historical-replay
```

or directly with:

```bash
node pcc-uniform-locked-nand-threshold0.mjs --json --historical-replay
```

This artifact surface discharges `UFS-003-ThresholdEquivalenceAllInputs` only. It does not discharge residual-band minimization, unrestricted final soundness, or final theorem emission.
