# NAND direct-wire semantics artifacts

The NAND direct-wire semantics checker writes its generated verdict here:

```text
artifacts/nand-direct-wire-semantics/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run semantics:nand
```

The checker validates `semantics/nand-direct-wire-spec.json`, then runs executable seed examples through `semantics/nand-direct-wire-reference.mjs`. The reference evaluator validates topological direct-wire words, evaluates NAND truth tables, computes word size as NAND gate count, checks truth-table equivalence, and checks compatible replacement at the open-word boundary.

The accepted verdict is a seed semantics result:

```text
semanticsReady = true
fullSemanticsCoverageProved = false
```

Future PRs should extend this into exhaustive small-model coverage and locked-NAND SAT threshold verification.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
