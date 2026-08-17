# Lean canonical Packet typed-frontier route reflection

`lean/PNP/ResidualTerminalPacketFrontierRouteReflection.lean` removes the
sixth caller-controlled Packet faithfulness field. It wraps the selected
source checks with explicit source and selector frontier signatures of one
arbitrary type with decidable equality. The active grouped-family projection
computes `frontierChecked` from equality of those signatures while retaining
the established canonical colour, positive charge, source route, rank tag,
and exact residual-descent checks.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_typed_frontier_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family and selector-rank carrier, positive
Packet evidence plus accepted executable selector silence and HB
active-dependency closure yields:

- one canonical handle;
- one exact earliest route and matching `FailureAt` proof;
- proof that the route is not `.colour`, `.charge`, `.rank`, or `.exactRoute`;
- if the route is `.frontier`, proof that the supplied typed frontier
  signatures are unequal; and
- if the route is `.descent`, proof that the supplied residual transition is
  not decreasing in the exact ten-coordinate `RankWF` order.

## What is kernel checked

The 30 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketFrontierRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, `Quot.sound`, or both; none uses
`Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation shortcut.

The regression checks equal and unequal concrete signatures, exact frontier
route semantics, equal-signature exclusion, the four prior route exclusions,
descent nondecrease, and the HB endpoint. The hostile audit rejects restoration
of the caller frontier bit, weakening equality or inequality, lost route
evidence, fixed bounds, assumptions, and theorem-name overclaims.

## Exact non-claim

The source and selector frontier signatures are explicit inputs. This
milestone neither constructs them from terminal data nor binds them to the
manuscript's BN5 frontier coordinates or full frontier-faithful comparison.
Obligation, activation, direction, and budget remain supplied Boolean
boundaries. Those four remaining routes still lack complete external semantics
and integration into a decreasing global outcome system.

This milestone does not construct the grouped family, selector ranks, realizer
claims, blocker tables, or no-lower ledger; establish selector compatibility,
complete route silence, unconditional HB negative closure, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, CNF-SAT in P, or P = NP.
