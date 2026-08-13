# Lean fail-closed Packet selector source-payload realization

`lean/PNP/ResidualTerminalPacketSelectorPayloadRealization.lean` reconstructs
the next bounded Packet interface after the canonical handle codec. For every
accepted code, the total function returns its decoded handle, the exact cell at
that handle's position in the supplied grouped BN6 family, and the canonical
first original positive payload atom of that nonempty cell.

The function fails closed exactly when the existing canonical decoder fails.
Lean proves that every successful result:

- re-encodes to exactly the accepted input bitstring;
- names a cell in the original explicit grouped family;
- gives that cell's exact decoded footprint;
- names an atom in that original cell; and
- retains the atom's strictly positive mass.

Successful realization exists exactly for the prior finite payload-selector
predicate. `TerminalPacketEncodedSelectorConclusion.selectorPayloadRealizations`
therefore upgrades the pair, positive balanced-triple, and full-span branches
without changing their logical alternatives, and
`terminalBN6_packet_selector_payload_realizations` composes the full finite
BN6-to-Packet chain with this lookup.

Here “payload realization” means deterministic source-payload materialization
relative to an already supplied explicit grouped family. The bits still encode
only a unary list position; they do not serialize the cell, atom, or payload.
This is not the manuscript's gain-or-blocker selector realizer: it constructs no
replacement circuit, proves no selector faithfulness or compatibility, returns
no gain or typed blocker route, derives no grouped family, and supplies no bound
in encoded circuit size or polynomial generation/runtime theorem. PkgC,
ZeroSlack, PCCMin, SAT in P, the remaining project assumptions, and `P = NP`
remain open.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorPayloadRealizationAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorPayloadRealization.lean
node --test audits/lean-residual-terminal-packet-selector-payload-realization0.test.mjs
```
