# Lean canonical finite Packet selector handles

`lean/PNP/ResidualTerminalPacketSelectorHandles.lean` reconstructs the next
bounded Packet edge after exact finite selector-universe membership. It gives
every footprint in an explicit grouped BN6 family a canonical finite handle:
a position in that family's duplicate-free grouped-footprint list.

The total decoder reads the footprint at that position. Exact grouping proves
the decoder injective, so a payload selector has exactly one handle. Each
decoded footprint mechanically retains:

- membership in the same exact grouped-footprint universe;
- containment in the family's common anchor carrier;
- length at least two; and
- an original grouped cell and atom payload witness.

`TerminalPacketPayloadSelectorConclusion.selectorHandles` upgrades every
existing branch without changing its alternatives. Pair and full-span packets
receive a handle for the same footprint. A positive balanced-triple packet
receives a handle for every supported pair footprint. The composed theorem
`terminalBN6_packet_selector_handles` performs BN6 classification, seed
extraction, exact universe membership, and canonical handle construction over
the same arbitrary finite grouped family.

These canonical finite Packet selector handles are input-relative list
positions, not the manuscript's bit encoding or a polynomially enumerable
selector universe. Injective decoding is not manuscript-level selector
faithfulness or compatibility. This module does not construct a selector
realizer or route, derive the grouped family from a terminal candidate,
establish polynomial encoding length or runtime, complete PkgC, ZeroSlack, or
PCCMin, put SAT in P, or prove `P = NP`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorHandlesAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorHandles.lean
node --test audits/lean-residual-terminal-packet-selector-handles0.test.mjs
```
