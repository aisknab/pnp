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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-11-128` records
27,442 declarations, 14,309 theorems, 7,290 assumption-free theorems, 14,999
excluded private declarations, 246 source-closure modules, and 2,548 reviewed
milestone candidates. Its 17,726,895 canonical bytes have SHA-256
`612342db90e5887e2da6417963946437c82a14003f48deeddeae03d50caf637f`;
the exact Lean source closure has SHA-256
`4fde46c2f495422c43f5d2eb3ed80500c097a94b511aaecc74f5e8da979cd910`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-11-129`
contains 107 milestones: 105 earned and two deliberately unearned. It pins
2,548 theorem types; its 826,175 bytes have SHA-256
`9093dd1bdc84405be1748831ad59b98a60aabbd80d389f26f38f889de44770ea`.
The BN6 bridge contributes eight reviewed theorem types.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-129` remains
fail-closed with all four disclosed project assumptions, all five blockers,
unset activation fingerprints, and absent `PNP.Main.p_eq_np`. Its 2,076,560
bytes have SHA-256
`79c3ef6dace2f95cdad66add48c105e4ed5f95609b9c2819533685f63ed941aa`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-129` has a
217,706-byte TeX source with SHA-256
`e43ad410bc6e10f4e5d22d24c559b236e5698eb54b8b6b2659e2d0b3a8e4989c`
and a deterministic 85-page, 455,104-byte A4 PDF with SHA-256
`f48bc615866790d08151198272e89c9e68f8e1fd404ae46700ced768f42aa70c`.

This closes the finite V54-to-V53 bridge and the resulting packet
classification for an explicit grouped survivor family. It does not construct PkgC,
derive or group survivors from a terminal candidate, establish the full
historical BN6 theorem, complete the Packet selector universe or realizer
routes, prove polynomial generation or runtime, prove ZeroSlack or PCCMin, put
SAT in P, or prove `P = NP`.
