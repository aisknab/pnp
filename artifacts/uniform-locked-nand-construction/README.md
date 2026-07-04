# Uniform locked NAND construction artifacts

The checker writes its generated verdict here:

```text
artifacts/uniform-locked-nand-construction/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-locked-nand-construction
```

or directly with:

```bash
node pcc-uniform-locked-nand-construction0.mjs --json
```

This artifact surface discharges `UFS-002-LockedNANDConstructionUniformPolynomial` only. It does not discharge threshold equivalence, residual-band minimization, unrestricted final soundness, or final theorem emission.
