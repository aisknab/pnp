# Uniform locked NAND construction artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/uniform-locked-nand-construction/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-locked-nand-construction -- --historical-replay
```

or directly with:

```bash
node pcc-uniform-locked-nand-construction0.mjs --json --historical-replay
```

This artifact surface discharges `UFS-002-LockedNANDConstructionUniformPolynomial` only. It does not discharge threshold equivalence, residual-band minimization, unrestricted final soundness, or final theorem emission.
