# Lean typed-direction Packet route reflection

`lean/PNP/ResidualTerminalPacketDirectionRouteReflection.lean` binds the
active Packet direction check to two explicit values in an arbitrary direction
type. The canonical grouped-family projection computes `directionChecked`
from exact equality of the source and selector directions while preserving the
computed BN5 frontier, obligation, and BN4 activation checks, canonical
colour, positive charge, the internal source route, the table-owned rank, and
exact residual descent.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_direction_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family, selector-rank carrier, and typed
direction domain with decidable equality, positive Packet evidence plus
accepted executable selector silence and HB active-dependency closure yields:

- one canonical handle;
- one exact earliest route with its matching `FailureAt` proof;
- proof that the route is not `.colour`, `.charge`, `.rank`, or
  `.exactRoute`;
- exact BN5 frontier inequality if the route is `.frontier`;
- prior frontier equality and exact BN5 obligation inequality if the route is
  `.obligation`;
- prior frontier and obligation equality plus exact BN4 activation-atom
  inequality if the route is `.activation`;
- prior frontier, obligation, and activation equality plus typed-direction
  inequality if the route is `.direction`; and
- exact ten-coordinate residual nondecrease if the route is `.descent`.

## What is kernel checked

The direction checker accepts exactly when the explicit source and selector
direction values are equal. Rejection is exactly typed-direction inequality;
the inherited caller-supplied direction Boolean is not consulted. Exact
first-route priority records all earlier checks before a direction failure.

The 35 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketDirectionRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, `Quot.sound`, or both; none uses
`Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation shortcut.

The regression separates equal directions and an independent direction
mismatch while deliberately setting the inherited direction bit false. It
checks first-route priority, all four canonical route exclusions, descent
nondecrease, and the positive Packet/HB endpoint. The hostile audit rejects a
restored caller-controlled bit, erased typed equality, weakened direction
evidence, fixed bounds, assumptions, and theorem-name overclaims.

## Exact non-claim

The two typed direction values remain explicit inputs; this milestone does not
construct them from terminal data or prove that they implement the
manuscript's complete `Dir(u)` semantics. Budget is the sole remaining supplied
Boolean boundary, and its route still lacks complete external semantics and
integration into a decreasing global outcome system.

This milestone does not construct the grouped family, selector ranks, realizer
claims, blocker tables, or no-lower ledger; establish selector compatibility,
complete route silence, unconditional HB negative closure, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, CNF-SAT in P, or P = NP.
