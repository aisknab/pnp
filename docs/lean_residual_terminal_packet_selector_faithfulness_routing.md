# Residual-terminal Packet selector-faithfulness routing

`lean/PNP/ResidualTerminalPacketSelectorFaithfulnessRouting.lean`
reconstructs the next Packet-to-HB edge named by the Pair packet seed,
Balanced-triple seed, Full-span spine seed, and patched BCEL seed results in
Section 16 of the pinned legacy manuscript. It connects an existing positive
BN6 Packet conclusion to the executable selector-silence induction through a
checked canonical-payload boundary.

## Data-only payload boundary

`TerminalPacketSelectorFaithfulnessPayload` contains ten explicit checks:
colour, frontier, charge, obligation, activation, direction, budget, exact
finite rank, exact route clearance, and strict descent clearance. There is no
caller-supplied faithful flag. The `check_eq_true_iff` theorem proves that the
Boolean checker accepts exactly their propositional conjunction.

`firstRoute` traverses the same fields in one fixed fail-closed order and
returns the first typed failure route. An accepted payload has no route, while
every returned route proves that the payload checker is false.

## Canonical Packet routing

For each input-relative canonical handle,
`packetSelectorPayloadFaithful` checks the existing canonical positive source
payload returned by `packetSelectorPayloadAtom` at that handle's supplied
finite rank. `checkPacketSelectorRoutesClear` exhaustively scans the complete
`packetSelectorHandles` list. Its equivalence theorem covers every handle,
rather than a selected prefix or caller-supplied subset.

The existing HB realizer environment already contains a faithfulness Boolean.
`checkPacketSelectorFaithfulnessBinding` exhaustively requires that Boolean to
equal the newly computed canonical-payload result at every handle. It cannot be
silently replaced by an independent table.

## Positive Packet contradiction

Every branch of `TerminalPacketSelectorHandleConclusion` supplies a canonical
handle. Pair and full-span branches expose their existing witness directly;
the balanced-triple branch uses the first two atoms of the proved
three-element carrier and its existing all-pairs handle theorem. Hence every
positive `TerminalBN6PacketConclusion` has a canonical handle.

Route-clear acceptance and exact HB binding make that handle environment
faithful. The named
`terminalBN6_packet_selector_faithfulness_hb_contradiction` theorem composes
this result with accepted executable HB selector silence and checked active
dependency closure, which prove every canonical handle nonfaithful. The two
equations yield `False`.

## Audit surface

The source-derived axiom transcript covers all 20 public declarations in the
module. The reviewed milestone theorems use only Lean's approved standard
axiom closure and do not reach `Classical.choice`, `sorryAx`, or a
project-specific axiom.

Run the focused checks with:

```text
lake build PNP.ResidualTerminalPacketSelectorFaithfulnessRouting
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorFaithfulnessRoutingAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorFaithfulnessRouting.lean
node --test audits/lean-residual-terminal-packet-selector-faithfulness-routing0.test.mjs
```

## Boundary

The grouped family, payload field Booleans, finite rank tags, route-clear
checks, exact binding, realizer claims, blocker activity, dependency rows, and
finite-to-exact rank map remain explicit terminal-relative inputs. The module
checks them but does not derive them from a terminal candidate or prove their
external manuscript semantics.

In particular, positive residual slack, `SaturatePositive`, `BCELReady`, the
grouped family, the route-clear payload data, and the no-lower ledger remain
open. This result does not establish unconditional HB negative closure,
complete route silence, unconditional ZeroSlack or PCCMin, encoded-size or
polynomial-runtime bounds, CNF-SAT in P, removal of a project assumption, or
`P = NP`.
