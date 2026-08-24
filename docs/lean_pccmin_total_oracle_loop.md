# Proof-bearing PCCMin total-oracle loop

M189 formalizes the report's general recursive PCCMin control flow over an
explicit proof-bearing oracle. It is a control-flow theorem, not a construction
of the remaining oracle.

`PNP.DirectWire.PCCMinOracleOutcome current` has exactly three outcomes:

- a next implementation with a `StrictEquivalentGain` proof;
- an `ExactMinimumResult`; or
- a `ZeroSlackResult`.

There is no unresolved or unchecked-success outcome. `PCCMinTotalOracle.route`
is polymorphic over arbitrary finite direct-wire input and output dimensions and
every current implementation. `runPCCMinTotalOracleLoop` follows strict gains
recursively and terminates on `residualSlack current`, using the checked strict
descent contained in each gain response.

The compiled endpoint
`PNP.DirectWire.pccmin_total_oracle_loop_checked_complete` proves that the
returned implementation:

- is semantically equivalent to the starting implementation;
- is globally semantically minimum;
- has the exhaustive reference-minimum gate count;
- has zero residual slack; and
- was reached through no more strict-gain iterations than the starting residual
  slack.

The regression fixtures use exhaustive reference minimization only to exercise
all three typed outcomes and the general recursion. They are not polynomial
algorithms and do not provide an active PCCMin implementation.

M189 does not construct or supply the total oracle, derive its terminal data,
prove unconditional ZeroSlack, encode the loop as a raw machine, bound the cost
of producing an oracle response, or establish encoded-size polynomial runtime
or certificate bounds. It therefore does not close a fixed risk-weighted
checkpoint or a global gate. The proof-completion estimate remains 35 percent;
formal artefact coverage changes independently.

## Verification

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinTotalOracleLoopAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinTotalOracleLoop.lean
node --test audits/lean-pccmin-total-oracle-loop0.test.mjs
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
```

The current checkpoint definitions and unchanged score are recorded in
[`status/PROOF_PROGRESS.json`](../status/PROOF_PROGRESS.json).
