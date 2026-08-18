# Lean BN4 activation-exact Packet route reflection

`lean/PNP/ResidualTerminalPacketBN4ActivationRouteReflection.lean` binds
the active Packet activation check to the nested BN4 activation key already
retained by each typed terminal BN5 coordinate. The canonical grouped-family
projection computes `activationChecked` from exact equality of the source and
selector activation atoms while preserving the computed BN5 frontier and
obligation checks, canonical colour, positive charge, the internal source
route, the table-owned rank, and exact residual descent.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_bn4_activation_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family and selector-rank carrier, positive
Packet evidence plus accepted executable selector silence and HB
active-dependency closure yields:

- one canonical handle;
- one exact earliest route with its matching `FailureAt` proof;
- proof that the route is not `.colour`, `.charge`, `.rank`, or
  `.exactRoute`;
- exact BN5 frontier inequality if the route is `.frontier`;
- prior frontier equality and exact BN5 obligation inequality if the route is
  `.obligation`;
- prior frontier and obligation equality plus exact BN4 activation-atom
  inequality if the route is `.activation`; and
- exact ten-coordinate residual nondecrease if the route is `.descent`.

## What is kernel checked

The activation checker accepts exactly when the two nested BN4 activation
atoms are equal. The existing BN4 activation theorem upgrades that equality to
extensional agreement of the canonical activation predicates on every cut.
Rejection is therefore exactly failure of that extensional boundary, without
enumerating the cut universe.

The 34 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketBN4ActivationRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, `Quot.sound`, or both; none uses
`Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation
shortcut.

The regression separates equal coordinates and independent frontier,
obligation, and activation mismatches. It checks activation-predicate
equivalence, first-route priority, all four canonical route exclusions,
descent nondecrease, and the positive Packet/HB endpoint. The hostile audit
rejects caller-controlled activation bits, erased activation semantics,
weakened route evidence, fixed bounds, assumptions, and theorem-name
overclaims.

## Exact non-claim

The typed BN5 coordinates remain explicit inputs; this milestone does not
construct them from terminal data or prove the manuscript's complete BN4,
BN5, or Packet adequacy bridge. Direction and budget are the two remaining
supplied Boolean boundaries, and their two routes still lack complete external
semantics and integration into a decreasing global outcome system.

This milestone does not construct the grouped family, selector ranks, realizer
claims, blocker tables, or no-lower ledger; establish selector compatibility,
complete route silence, unconditional HB negative closure, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, CNF-SAT in P, or P = NP.
