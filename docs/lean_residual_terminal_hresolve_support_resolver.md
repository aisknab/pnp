# Terminal-derived HResolve support resolver

`lean/PNP/ResidualTerminalHResolveSupportResolver.lean` removes the supplied
candidate-family and supplied constructive-predicate boundary from the finite
HResolve interface for canonical terminal supports.

For every finite direct-wire candidate, the candidate family is exactly
`allTerminalSupportSeeds` over its complete primitive-record universe. Lean
proves this family duplicate-free and proves that every Boolean-selected
canonical seed occurs in it. Each seed is saturated through
`terminalCandidateSaturationSystem`, so no arbitrary dependency relation is
accepted by the resolver.

The resolver then extracts the saturated open support and computes its actual
reference residual slack. Zero slack is the exact route; positive slack is the
gain route. Existing global semantic theorems turn those tests into:

- `IsSemanticallyMinimum` for an exact route; or
- an existential `StrictEquivalentGain` witness for a gain route.

The named endpoint
`terminal_hresolve_support_resolver_constructive_complete` proves that every
member of the terminal-derived, duplicate-free family receives one of those
two proof-bearing constructive routes. There is no caller-supplied family,
exact predicate, gain predicate, route tag, blocker predicate, or success flag.

This is an exhaustive reference resolver, not the full manuscript HResolve
algorithm. Canonical subset enumeration and reference minimization may be
exponential. The result does not formalize the HN grammar, BWL, ParseOrExit,
H-disjointness, blocker dependency semantics, or a NoHereditary sidecar, and it
does not cover hereditary candidates beyond the canonical terminal support
seed universe. Polynomial HResolve, BudgetResolve, the complete no-lower
ledger, unconditional ZeroSlack, polynomial PCCMin, SAT in P, and P = NP remain
open.

The milestone is audited by:

```bash
lake env lean -DwarningAsError=true \
  lean-audit/PNPResidualTerminalHResolveSupportResolverAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPResidualTerminalHResolveSupportResolver.lean
node --test \
  audits/lean-residual-terminal-hresolve-support-resolver0.test.mjs
```
