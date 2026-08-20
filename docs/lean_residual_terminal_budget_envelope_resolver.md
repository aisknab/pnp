# Terminal budget-envelope resolver

`PNP.DirectWire.resolveTerminalBudgetEnvelope` adds a finite, executable
budget boundary on top of the terminal-derived HResolve support universe.
`TerminalSupportBudget.Fits` recomputes three facts for each canonical seed:
the candidate-derived saturated extraction has at least one NAND gate, has at
least one terminal interface coordinate, and respects both the supplied gate
and saturated-record caps.

The resolver scans every canonical terminal support seed. A returned support
carries membership and exact feasibility proofs. Search failure is reflected
by `findTerminalBudgetFeasibleSupport_eq_none_iff`, which excludes every seed
using the same computed predicate and therefore supplies the finite strong
`NoBudget` branch without a caller success bit or prefiltered family.

For a feasible support, actual residual slack selects the route. Zero slack is
reflected to semantic minimality; positive slack supplies a genuine strictly
smaller equivalent implementation. The endpoint
`terminal_budget_envelope_resolver_constructive_complete` returns exactly one
of those constructive possibilities or complete envelope exclusion.

This is an exhaustive reference resolver. The budget caps remain inputs, and
the subset scan, saturation, and reference minimization may be exponential. It
does not implement the manuscript's HN/BUD grammar, BWL or budget-envelope
dynamic program, blocker dependencies, polynomial BudgetResolve, the complete
no-lower ledger, unconditional ZeroSlack, PCCMin, SAT in P, or `P = NP`.
