# Lean typed-budget Packet route reflection

`lean/PNP/ResidualTerminalPacketBudgetRouteReflection.lean` binds the active
Packet budget check to two explicit values in an arbitrary budget type. The
canonical grouped-family projection computes `budgetChecked` from exact
equality of the source and selector budgets while preserving the computed BN5
frontier and obligation checks, BN4 activation, typed direction equality,
canonical colour, positive charge, the internal source route, the table-owned
rank, and exact residual descent.

The main endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_budget_reflected_hb_first_route_failure
```

For an arbitrary finite grouped BN6 family, selector-rank carrier, and typed
budget domain with decidable equality, positive Packet evidence plus accepted
executable selector silence and HB active-dependency closure yields:

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
  inequality if the route is `.direction`;
- all four prior equalities plus typed-budget inequality if the route is
  `.budget`; and
- exact ten-coordinate residual nondecrease if the route is `.descent`.

## What is kernel checked

The budget checker accepts exactly when the explicit source and selector
budget values are equal. Rejection is exactly typed-budget inequality; the
inherited caller-supplied budget Boolean is not consulted. Exact first-route
priority records every earlier check before a budget failure.

The 37 public declarations are printed by
`lean-audit/PNPResidualTerminalPacketBudgetRouteReflectionAxiomAudit.lean`.
Their closures are empty, `propext`, `Quot.sound`, or both; none uses
`Classical.choice`, a project axiom, `sorryAx`, or a host-evaluation shortcut.

The regression separates equal budgets and an independent budget mismatch
while deliberately setting the inherited budget bit false. It checks
first-route priority through `.budget`, all four canonical route exclusions,
descent nondecrease, and the positive Packet/HB endpoint. The hostile audit
rejects a restored caller-controlled bit, erased typed equality, weakened
budget evidence, fixed bounds, assumptions, and theorem-name overclaims.

## Exact non-claim

The two typed budget values remain explicit inputs. This milestone does not
construct them from terminal data, prove that they implement the manuscript's
complete `Bud(u)` envelope semantics, or identify local Packet budget
coherence with BudgetResolve or HB `budgetActive` semantics. Computing all ten
local classifier fields is not evidence that terminal construction supplies
adequate values or that every external route is globally silent.

This milestone does not construct the grouped family, selector ranks, realizer
claims, blocker tables, or no-lower ledger; establish selector compatibility,
complete route silence, unconditional HB negative closure, ZeroSlack, PCCMin,
encoded-size or polynomial-runtime bounds, CNF-SAT in P, or P = NP.
