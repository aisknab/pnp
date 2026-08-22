# Same-family Selector/HB, Packet, and BCEL ZeroSlack coherence

`PNP.ResidualTerminalZeroSlackPacketSelectorHBCoherence` removes the
detached Selector/HB certificate that the report-facing `ZeroSlackCertificate`
previously stored beside its Packet/budget certificate. The accepted M180
certificate already recomputes selector faithfulness and checks selector
silence plus HB no-outcome closure. M182 derives the public Selector/HB
sidecar directly from that exact grouped family, computed realizer table, and
dependency table.

The definitional identity theorems
`PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_family`,
`selectorHB_realizerTable`, and `selectorHB_dependencyTable` make the
same-family boundary reviewable without a caller-supplied equality proof,
digest, success Boolean, or duplicate data field. The endpoint
`PNP.packet_selector_hb_bcel_coherent_checked_complete` combines selector
nonfaithfulness, valid HB closure, all-node inactivity, positive-Packet
exclusion, and the dependent BCEL constant-activation contradiction for that
one certificate. The report-facing
`PNP.zeroslack_packet_selector_hb_bcel_coherent_checked_complete` exposes
the same result through `ZeroSlackCertificate`.

The grouped family and all terminal, budget, Packet, realizer, dependency,
rank, and BCEL inputs remain supplied. This milestone does not derive those
inputs or BCEL constant activation from positive residual slack, complete the
manuscript no-lower ledger, establish unconditional ZeroSlack or PCCMin, prove
polynomial runtime, put SAT in P, remove a project assumption, or prove
`P = NP`.

## Verification

```bash
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalZeroSlackPacketSelectorHBCoherenceAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalZeroSlackPacketSelectorHBCoherence.lean
node --test audits/lean-residual-terminal-zeroslack-packet-selector-hb-coherence0.test.mjs
```

The axiom audit follows all public definitions and theorems introduced at this
boundary. The hostile audit rejects detached family, table, or dependency data;
caller-supplied coherence devices; fixed carrier bounds; and theorem
overclaims.
