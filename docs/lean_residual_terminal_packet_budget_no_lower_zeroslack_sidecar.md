# Proof-bearing Packet/budget no-lower ZeroSlack sidecar

`lean/PNP/ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar.lean` replaces
the report-facing `noLowerRouteLedgerComplete` string with one checked,
proof-bearing boundary.

The sidecar stores arbitrary finite typed data:

- one direct-wire candidate and its candidate-derived saturation model;
- one finite terminal support budget;
- one grouped Packet family and typed-realizer table over that same candidate;
- one exact-rank dependency table and before/after residual-rank maps; and
- the exact equation that the existing Packet/budget no-lower composition
  returned `true`.

`packet_budget_no_lower_zeroslack_sidecar_checked_complete` reflects that
equation through the existing component theorems. It proves that every
budget-feasible governed support is semantically minimum, no such support has
a strict equivalent gain, and the supplied grouped family has no positive
Packet conclusion. No caller Boolean, string ledger handle, or caller-supplied
conclusion is accepted.

The budget caps, grouped family, typed payloads, finite ranks, realizer claims,
activity environment, dependency rows, and rank maps remain supplied. This is
the existing finite Packet and budget-support composition, not the manuscript's
complete no-lower ledger. It does not cover normalization, HResolve,
saturation-loss, named-route, or replay rows; construct terminal data; prove
Packet adequacy; establish unconditional ZeroSlack or PCCMin; prove polynomial
size or runtime; put SAT in P; remove a project axiom; or prove `P = NP`.

Review with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecarAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketBudgetNoLowerZeroSlackSidecar.lean
node --test audits/lean-residual-terminal-packet-budget-no-lower-zeroslack-sidecar0.test.mjs
```
