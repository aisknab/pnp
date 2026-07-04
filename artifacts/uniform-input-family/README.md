# Uniform input family artifacts

The checker writes its generated verdict here:

```text
artifacts/uniform-input-family/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-input-family
```

or directly with:

```bash
node pcc-uniform-input-family0.mjs --json
```

This artifact surface discharges `UFS-001-InputFamilyUniformity` only. It does not discharge locked NAND construction, threshold equivalence, residual-band minimization, unrestricted final soundness, or final theorem emission.
