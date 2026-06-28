# Locked NAND SAT small-model artifacts

The locked NAND SAT small-model checker writes its generated verdict here:

```text
artifacts/locked-nand-sat-small-models/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run semantics:locked-nand:sat-small-models
```

The audit validates `semantics/locked-nand-sat-small-models-config.json`, enumerates the configured small CNF universe, computes brute-force SAT, builds a locked final-output NAND word for each seed formula, evaluates its truth table, performs exact small-model minimization inside the configured gate bound, and checks that the threshold predicate agrees with brute-force SAT.

The accepted verdict is a bounded seed result:

```text
satSmallModelsReady = true
fullLockedNANDThresholdCoverageProved = false
```

Future PRs should expand this into locked NAND macro truth-table verification, prefix conjunction checks, final-lock separation, baseline distinctness, and the full locked NAND threshold theorem.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
