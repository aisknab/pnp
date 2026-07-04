# Uniform locked NAND threshold artifacts

The checker writes its generated verdict here:

```text
artifacts/uniform-locked-nand-threshold/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-locked-nand-threshold
```

or directly with:

```bash
node pcc-uniform-locked-nand-threshold0.mjs --json
```

This artifact surface discharges `UFS-003-ThresholdEquivalenceAllInputs` only. It does not discharge residual-band minimization, unrestricted final soundness, or final theorem emission.
