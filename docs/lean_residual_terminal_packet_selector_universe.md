# Lean finite Packet payload-selector universe

`lean/PNP/ResidualTerminalPacketSelectorUniverse.lean` reconstructs the next
bounded Packet edge after raw selector-seed extraction. It defines the exact
finite payload-selector universe of an explicit grouped BN6 family as the list
of that family's grouped cell footprints.

The universe is duplicate-free because exact grouping already requires unique
footprints. Membership is equivalent to naming an original grouped cell at the
same footprint. `HasPacketPayloadSelectorAt` combines that membership with the
existing raw seed facts:

- the footprint remains inside the same anchor carrier;
- it contains at least two anchors; and
- it retains an original grouped cell and atom payload witness.

`TerminalPacketSelectorSeedConclusion.payloadSelectors` upgrades every seed
branch without changing its logical alternatives. Pair and full-span packets
receive one member at the same footprint. A positive balanced-triple packet
receives a member for every supported pair footprint. The composed theorem
`terminalBN6_packet_payload_selectors` performs BN6 classification, seed
extraction, and finite-universe membership over the same arbitrary grouped
family.

The term "payload selector" is intentionally local to this finite interface.
This is not yet the manuscript's encoded or polynomial selector universe, and
payload retention is not manuscript-level selector faithfulness. The module
does not prove selector compatibility, construct a realizer or route, derive
the grouped family from a terminal candidate, establish polynomial enumeration
or size bounds, complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove
`P = NP`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorUniverseAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorUniverse.lean
node --test audits/lean-residual-terminal-packet-selector-universe0.test.mjs
```
