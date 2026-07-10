# Uniform complexity conclusion artifacts

> Historical assertion-checker artifact. It is subordinate to `status/FORMAL_RECONSTRUCTION_STATUS.json`.

The checker writes its generated verdict here:

```text
artifacts/uniform-complexity-conclusion/latest-verdict.json
```

Run it with:

```bash
npm run proof:uniform-complexity-conclusion -- --historical-replay
```

or directly with:

```bash
node pcc-uniform-complexity-conclusion0.mjs --json --historical-replay
```

This artifact surface discharges `UFS-007-ComplexityConclusionUniform` only. It does not discharge `Release.UnrestrictedFinalSoundness`, activate public theorem emission, or publish the final theorem release transition.
