# Lean finite BN6 hypergraph packet bridge

`lean/PNP/ResidualTerminalBN6HypergraphPacket.lean` reconstructs the
manuscript's finite BN6 hypergraph-packet edge over an arbitrary finite anchor
carrier. It consumes an explicit already-grouped family of positive residual
cells. Each group retains a verified V54 minimal-consumer system, the exact
PkgC singletonization premise, a nonempty positive integer atom ledger, and
concrete payload data.

For each group, V54 proves that two-sided request activation is exactly the
cut indicator of its singleton footprint. The new bridge proves that this is
also the crossing predicate of the corresponding V53 hyperedge. Summing the
pointwise equalities constructs a sparse nonnegative hypergraph whose cut
weight is exactly the original activation weight. A supplied BCEL-ready
constant-activation equation therefore becomes V53's constant-proper-cut
premise without sampling a fixed carrier.

The named theorem `PNP.DirectWire.terminalBN6_hypergraph_packet` applies V53
and returns the complete cardinality classification:

- at two anchors, a positive full-carrier pair packet;
- at three anchors, a common pair mass `p`, the exact equation
  `w_A + 2p = D`, and conditional payload witnesses for both the balanced
  triple and full-span packets, so the mixed three-anchor case is preserved;
- at four or more anchors, zero mass at every proper footprint and one
  positive full-span packet.

Positive grouped footprint mass cannot lose its source evidence: the theorem
extracts an original payload-bearing atom from the corresponding group for
every emitted packet footprint. The atom type, payload type, carrier, group
count, and anchor cardinality are arbitrary. No `Fin` instance or hard-coded
cut occurs in the production source.

The regression exercises two-anchor, mixed three-anchor, and four-anchor
families. Hostile cases show that repeated footprints are not an exact
grouping, a disjoint nonsingleton consumer cannot satisfy the V54 premise, and
unequal pair masses fail the constant-cut equation. The axiom transcript
covers all 21 public declarations and admits only `propext` and `Quot.sound`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalBN6HypergraphPacketAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalBN6HypergraphPacket.lean
node --test audits/lean-residual-terminal-bn6-hypergraph-packet0.test.mjs
```

## Mechanically generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-12-129` records
27,573 declarations, 14,360 theorems, 7,314 assumption-free theorems, 15,002
excluded private declarations, 247 source-closure modules, and 2,557 reviewed
milestone candidates. Its 17,787,380 canonical bytes have SHA-256
`859ef0595f1eeea872518b0f399a788225e3a2ed9fefe987c6ae5bd6b3783aaf`;
the exact Lean source closure has SHA-256
`4608b17afe6e8d0be3f7f6e0fae526025c0050f64dca9670e71ae89f9f27aa7c`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-12-130`
contains 108 milestones: 106 earned and two deliberately unearned. It pins
2,557 theorem types; its 829,327 bytes have SHA-256
`f076b8f813c2877d7a03b7090151d4c9db9f4793a5c4f40fbdc5125c82808ed8`.
The BN6 bridge contributes eight reviewed theorem types.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-130` remains
fail-closed with all four disclosed project assumptions, all five blockers,
unset activation fingerprints, and absent `PNP.Main.p_eq_np`. Its 2,084,476
bytes have SHA-256
`1a4609a63dd44da92cfc4558d1cef0db60430b26942cc6b3e2d199eb35d66ed9`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-130` has a
218,897-byte TeX source with SHA-256
`2f3aeaa0801283edbcb713f74567d133ea4598e3b5eb04541ac083d31fbf7546`
and a deterministic 85-page, 455,853-byte A4 PDF with SHA-256
`fedbffc7877c0cf4da70f6eea77395f7ee413e48917a80ee3ea5f24d9c325fec`.

This closes the finite V54-to-V53 bridge and the resulting packet
classification for an explicit grouped survivor family. It does not complete PkgC,
derive or group survivors from a terminal candidate, establish the full
historical BN6 theorem, complete the Packet selector universe or realizer
routes, prove polynomial generation or runtime, prove ZeroSlack or PCCMin, put
SAT in P, or prove `P = NP`.
