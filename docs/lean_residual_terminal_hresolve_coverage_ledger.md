# Checked finite HResolve coverage ledger

`lean/PNP/ResidualTerminalHResolveCoverageLedger.lean` replaces the old
string-only HResolve sidecar boundary with one bounded executable theorem
surface over an arbitrary supplied finite candidate family.

For each supplied candidate, Lean computes one of four routes in fixed order:

```text
exact -> gain -> blocked -> unresolved
```

The generated route ledger maps that classifier across the entire supplied
list. The NoHereditary sidecar checker independently verifies that the list has
no duplicate candidates and that every candidate is classified `blocked`.
The reflection theorem proves this is equivalent to every listed candidate
having neither an exact route nor a gain route and carrying a positive blocker
predicate. Soundness and completeness theorems tie every ledger row to exactly
the supplied enumeration, and the named endpoint shows accepted sidecar data
excludes both constructive routes for every listed candidate.

This is finite-family coverage, not the full manuscript HResolve theorem. The
candidate family and the decidable exact, gain, and blocker predicates are
supplied. The result does not construct the governed family from terminal data
or prove HN grammar coverage, BWL exactness, H-disjointness, exact-minimum or
strict-gain semantics, blocker dependency semantics, or completeness outside
the supplied enumeration. BudgetResolve, normalization, other no-lower rows,
saturation, replay, unconditional ZeroSlack, and polynomial PCCMin remain open.

The milestone is audited by:

```bash
lake env lean -DwarningAsError=true \
  lean-audit/PNPResidualTerminalHResolveCoverageLedgerAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPResidualTerminalHResolveCoverageLedger.lean
node --test \
  audits/lean-residual-terminal-hresolve-coverage-ledger0.test.mjs
```
