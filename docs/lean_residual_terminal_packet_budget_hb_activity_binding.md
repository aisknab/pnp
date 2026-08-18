# Checked Packet budget/HB activity binding

This milestone closes one local dependency edge between the typed Packet
budget route and the finite HB blocker table. It does not claim the global
ZeroSlack result.

## Exact checked interface

For every canonical handle in an arbitrary finite grouped BN6 family,
`checkPacketBudgetHBActivityBinding` checks:

```text
sourceBudget = selectorBudget
or
budgetActive(rankOf(handle)) = true
```

The handle list is the family's existing complete input-relative enumeration,
and `rankOf` is the typed-realizer table's authoritative finite rank. There is
no separate success flag and no fixed selector or rank bound.

`checkPacketBudgetHBActivityBinding_eq_true_iff` proves that this Boolean scan
is exactly the proposition that every typed budget mismatch activates the
corresponding ranked HB budget node.

## Composition with HB closure

The existing `checkNoOutcomeActiveClosure` checker independently validates the
strict exact-rank dependency table and the local active-to-active closure
condition. Its well-founded induction theorem proves every HN and budget
activity bit false.

Therefore
`packetBudget_eq_of_checkedHBActivityBinding` combines the two accepted checks
to prove exact source/selector budget equality at every canonical handle.
`packetSelectorBudgetFirstRoute_ne_of_checkedHBActivityBinding` then proves
that the canonical first-route classifier cannot return `.budget`.

The named endpoint
`terminalBN6_packet_budget_hb_activity_bound_first_route_failure` composes this
with positive Packet existence and executable selector silence. The forced
route is one of `.frontier`, `.obligation`, `.activation`, `.direction`, or
`.descent`; `.colour`, `.charge`, `.rank`, `.exactRoute`, and `.budget` are
excluded. The existing `FailureAt` predicate retains the exact ordered field
meaning, and a `.descent` route still carries actual ten-coordinate
nondecrease.

## Audit surface

- `lean/PNP/ResidualTerminalPacketBudgetHBActivityBinding.lean`
- `lean-regression/PNPResidualTerminalPacketBudgetHBActivityBinding.lean`
- `lean-audit/PNPResidualTerminalPacketBudgetHBActivityBindingAxiomAudit.lean`
- `audits/lean-residual-terminal-packet-budget-hb-activity-binding0.test.mjs`

The regression accepts equality without activity, accepts inequality only
with the authoritative budget activity bit, rejects an inactive mismatch, and
shows that an active mismatch cannot simultaneously pass the independently
ranked no-outcome closure.

## Boundary

The grouped family, typed budgets, coordinates, directions, rank map, residual
ranks, realizer claims, activity table, dependency rows, and checked binding
remain explicit data. This milestone does not construct the binding or
`Bud(u)` envelope from terminal data, implement `BUD.BudgetResolver`, establish
budget-blocker semantic completeness, or derive the HB tables.

Frontier, obligation, activation, direction, and descent routes remain open.
The theorem does not prove complete Packet adequacy, unconditional HB negative
closure, the no-lower ledger, ZeroSlack, PCCMin, encoded-size or
polynomial-runtime bounds, SAT in P, removal of a project assumption, or
P = NP.
