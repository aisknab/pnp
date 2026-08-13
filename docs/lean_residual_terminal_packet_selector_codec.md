# Lean canonical Packet selector-handle codec

`lean/PNP/ResidualTerminalPacketSelectorCodec.lean` reconstructs the next
bounded Packet interface after canonical finite selector handles. Each handle
position `i` has the canonical unary code `i` one-bits followed by one zero
delimiter.

The total decoder fails closed on an absent delimiter, trailing data, and every
index outside the exact explicit grouped-footprint list. Lean proves exact
round trip, injective encoding, canonical re-encoding of every accepted input,
an exact `i + 1` code length, and a length bound by the family's selector-list
length. Every accepted code mechanically retains:

- exact payload-selector membership;
- containment in the family's common carrier;
- footprint length at least two; and
- the original grouped cell and atom payload witness.

Every exact payload selector has one unique accepted bitstring.
`TerminalPacketPayloadSelectorConclusion.selectorCodes` upgrades the pair,
positive balanced-triple, and full-span alternatives without changing their
logic, and `terminalBN6_packet_selector_codes` composes the full finite BN6-to-
Packet chain with this codec.

This is a canonical codec for input-relative list positions. Its length is
bounded by the explicit grouped-family list, not by encoded circuit size. It
does not establish a polynomial selector universe or generation/runtime bound,
encode atom or payload data, prove manuscript-level selector faithfulness or
compatibility, construct a selector realizer or route, derive the grouped
family, complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove `P = NP`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorCodecAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorCodec.lean
node --test audits/lean-residual-terminal-packet-selector-codec0.test.mjs
```
