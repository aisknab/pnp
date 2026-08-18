# Lean BN5-bound Packet frontier and obligation route reflection

`lean/PNP/ResidualTerminalPacketBN5ObligationRouteReflection.lean` binds two
active Packet checks to the typed terminal BN5 coordinate already retained by
the reconstruction. The canonical grouped-family projection computes both
`frontierChecked` and `obligationChecked` from exact equality of the source and
selector BN5 coordinate fields while preserving canonical colour, positive
charge, the internal source route, the table-owned rank, and exact residual
descent.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_bn5_frontier_obligation_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family and selector-rank carrier, positive
Packet evidence plus accepted executable selector silence and HB
active-dependency closure yields:

- one canonical handle;
- one exact earliest route with its matching `FailureAt` proof;
- proof that the route is not `.colour`, `.charge`, `.rank`, or `.exactRoute`;
- exact BN5 frontier inequality if the route is `.frontier`;
- prior frontier equality and exact BN5 obligation inequality if the route is
  `.obligation`; and
- exact ten-coordinate residual nondecrease if the route is `.descent`.

## What is kernel checked

The 36 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketBN5ObligationRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, `Quot.sound`, or both; none uses
`Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation shortcut.

The regression separates equal coordinates, a frontier-only mismatch, and an
obligation-only mismatch. It checks first-route priority, all four earlier
route exclusions, descent nondecrease, and the positive Packet/HB endpoint.
The hostile audit rejects caller-controlled frontier or obligation bits,
erased BN5 fields, weakened equality evidence, fixed bounds, assumptions, and
theorem-name overclaims.

## Exact non-claim

The typed BN5 coordinates remain explicit inputs; this milestone does not
construct them from terminal data or prove the manuscript's complete BN5 or
Packet adequacy bridge. Activation, direction, and budget are the three
remaining supplied Boolean boundaries and their three remaining routes still
lack complete external semantics and integration into a decreasing global
outcome system.

This milestone does not construct the grouped family, selector ranks, realizer
claims, blocker tables, or no-lower ledger; establish selector compatibility,
complete route silence, unconditional HB negative closure, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, CNF-SAT in P, or P = NP.
