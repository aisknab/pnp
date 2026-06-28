# NAND small-model artifacts

The NAND small-model checker writes its generated verdict here:

```text
artifacts/nand-small-models/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run semantics:nand:small-models
```

The audit validates `semantics/nand-small-models-config.json`, exhaustively enumerates one-output NAND direct-wire words inside the configured seed bounds, computes truth-table classes, computes brute-force minimum size inside the configured universe, and checks replacement compatibility for equivalent and non-equivalent same-boundary words.

The accepted verdict is a bounded small-model seed result:

```text
smallModelsReady = true
fullSmallModelCoverageProved = false
```

Future PRs should raise the bounds, add multi-output exhaustive slices, and connect the small-model universe to locked-NAND SAT-threshold tests.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
