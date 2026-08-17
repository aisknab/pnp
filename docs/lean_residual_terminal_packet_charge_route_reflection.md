# Lean canonical Packet charge-route reflection

`lean/PNP/ResidualTerminalPacketChargeRouteReflection.lean` removes one more
caller-controlled Packet faithfulness field. A canonical grouped-family handle
already selects an original payload atom carrying a proof that its mass is
strictly positive. The new projection therefore sets `chargeChecked` from that
canonical source fact while reusing the established source-route, rank-tag, and
RankWF-descent projections.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_charge_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family and selector-rank carrier, positive
Packet evidence plus accepted executable selector silence and HB
active-dependency closure yields:

- one canonical handle;
- one exact earliest route and matching `FailureAt` proof;
- proof that the route is not `.charge`, `.rank`, or `.exactRoute`; and
- if the route is `.descent`, proof that the supplied residual transition is
  not decreasing in the exact ten-coordinate `RankWF` order.

## What is kernel checked

The 27 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketChargeRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, or `propext` plus `Quot.sound`; none
uses `Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation
shortcut.

The regression covers a forged false charge bit, all six retained semantic
routes, a decreasing transition, an equal-rank descent failure, grouped-family
route exclusions, table preservation, and the HB endpoint. The hostile audit
rejects restoration of caller charge, omission of canonical positive-mass
evidence, reversed descent, lost route exclusions, fixed bounds, assumptions,
and theorem-name overclaims.

## Exact non-claim

Strictly positive source mass is not full external charge-surplus semantics,
not a proved replacement circuit, and not a budget or exact-minimum result.
Colour, frontier, obligation, activation, direction, and budget remain supplied
Boolean boundaries. Those six remaining routes still lack complete external
semantics and integration into a decreasing global outcome system.

This milestone does not establish selector compatibility, complete route
silence, unconditional HB negative closure, ZeroSlack, PCCMin, encoded-size or
polynomial-runtime bounds, CNF-SAT in P, or P = NP.
