# Lean finite Packet selector-seed extraction

`lean/PNP/ResidualTerminalPacketSelectorSeeds.lean` reconstructs the first
bounded Packet edge after the finite BN6 classification. It consumes any
`TerminalBN6PacketConclusion` over an arbitrary finite grouped family and
retains the existing source payload evidence as a raw selector seed.

A `HasPacketSelectorSeedAt` witness records three facts together:

- the footprint is a sublist of the same BN6 anchor carrier;
- the footprint has at least two anchors; and
- the footprint retains a concrete grouped cell and atom through
  `HasPayloadAt`.

`TerminalBN6PacketConclusion.selectorSeeds` is exhaustive over the existing
BN6 constructors. A pair packet yields a full-pair seed. A three-anchor packet
with positive common pair mass yields a seed for every supported pair
footprint. If only its full-span side is positive, it yields a full-span seed.
The four-or-more-anchor branch also yields a positive full-span seed. The
composed theorem `terminalBN6_packet_selector_seeds` applies the same
extraction directly after `terminalBN6_hypergraph_packet`.

The production theorem fixes no `Fin` carrier and makes no executable choice
from a proposition. The generic regression constructs each positive logical
branch without copying a fixed example family. The hostile audit rejects
mutations that erase carrier containment, weaken the footprint-size premise,
drop payload evidence, replace all-pair coverage by one existential seed, or
assume one side of the mixed three-anchor alternative. The exact
five-declaration axiom transcript admits only `propext` and `Quot.sound`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorSeedsAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorSeeds.lean
node --test audits/lean-residual-terminal-packet-selector-seeds0.test.mjs
```

This closes raw payload-backed Packet selector-seed input extraction only. It
does not prove selector-universe membership, selector faithfulness or
compatibility, construct a realizer or route, establish enumeration or a
polynomial bound, complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove
`P = NP`.
