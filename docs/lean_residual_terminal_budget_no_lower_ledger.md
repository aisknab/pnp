# Terminal budget no-lower ledger

`PNP.DirectWire.terminalBudgetNoLowerRouteLedger` materializes one route for
every seed in the complete canonical terminal support universe. The route is
computed from the M171 budget predicate and the saturated extracted support's
actual residual slack:

- a budget-feasible semantic minimum is `exact`;
- a budget-feasible strict equivalent gain is `gain`; and
- a support outside the same recomputed envelope is `noBudget`.

`checkTerminalBudgetNoLowerLedger` scans the complete canonical universe and
accepts exactly when no row is `gain`. Its reflection theorem identifies that
Boolean with semantic minimality of every governed budget-feasible support.
The endpoint
`terminal_budget_no_lower_ledger_excludes_feasible_gain` therefore returns
both the all-support minimum statement and exclusion of every governed,
budget-feasible strict-equivalent-gain witness.

This closes only a finite terminal-derived budget branch of the remaining
no-lower ledger. The budget caps remain supplied, and subset enumeration,
candidate-derived saturation, and reference minimization may be exponential.
It is not the manuscript's HN/BUD grammar, BWL or budget-envelope dynamic
program, blocker semantics, polynomial BudgetResolve, a composition with the
Packet or other no-lower branches, unconditional ZeroSlack, polynomial PCCMin,
SAT in P, or `P = NP`.
