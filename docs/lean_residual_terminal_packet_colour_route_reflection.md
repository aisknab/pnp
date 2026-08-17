# Lean canonical Packet colour-route reflection

`lean/PNP/ResidualTerminalPacketColourRouteReflection.lean` removes the first
caller-controlled Packet faithfulness field. Every canonical grouped-family
handle already decodes to a footprint proved to lie in the family carrier and
to contain at least two atoms. The new projection computes an internal colour
check from that selector-relevant size and retains the carrier-sublist proof,
while reusing the established positive-charge, source-route, rank-tag, and
RankWF-descent projections.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_colour_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family and selector-rank carrier, positive
Packet evidence plus accepted executable selector silence and HB
active-dependency closure yields:

- one canonical handle;
- one exact earliest route and matching `FailureAt` proof;
- proof that the route is not `.colour`, `.charge`, `.rank`, or `.exactRoute`;
  and
- if the route is `.descent`, proof that the supplied residual transition is
  not decreasing in the exact ten-coordinate `RankWF` order.

## What is kernel checked

The 31 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketColourRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, `Quot.sound`, or both; none uses
`Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation shortcut.

The regression shows that a forged caller colour bit is ignored, a false
computed colour check fails closed as `.colour`, the five retained semantic
routes still classify exactly, and grouped-family colour, charge, rank, and
source-route exclusions compose with the HB endpoint. The hostile audit rejects
restoration of caller colour, bypass of canonical footprint evidence, reversed
descent, lost route exclusions, fixed bounds, assumptions, and theorem-name
overclaims.

## Exact non-claim

The internal colour check proves only canonical grouped-footprint eligibility:
selector-relevant size together with separately retained carrier-sublist
membership. It is not the manuscript's full external colour equivalence.
Frontier, obligation, activation, direction, and budget remain supplied Boolean
boundaries. Those five remaining routes still lack complete external semantics
and integration into a decreasing global outcome system.

This milestone does not construct the grouped family, selector ranks, realizer
claims, blocker tables, or no-lower ledger; establish selector compatibility,
complete route silence, unconditional HB negative closure, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, CNF-SAT in P, or P = NP.
