# Finite BN5 full-shadow localization

## Earned scope

`lean/PNP/ResidualTerminalBN5FullShadowLocalization.lean` formalizes a finite
BN5 full-shadow localization kernel for arbitrary finite explicit inputs. It
starts from one complete BN4 cancellation key and a negative residual. Each
payload refines one unit of negative mass into a canonical indexed full unit
whose exact coordinate retains:

- the complete BN4 key;
- frontier data;
- charge-owner data;
- obligation data;
- origin-kernel data; and
- mode-projection data.

The quotient-shadow ledger uses the same coordinate type. Its edge relation is
literal coordinate equality, and its matching condition compares full and
shadow multiplicity in every full-unit fibre.

The total classifier has five proof-bearing outcomes. It reports no negative
residual, rejects a payload list whose length differs from the negative mass,
returns `cutSilent` only when the code is inactive at the cut, returns complete
multiplicity coverage, or returns a strict Hall deficit. A Hall deficit exposes
the full-unit fibre and its shadow-neighbor fibre, proves the latter has
strictly smaller cardinality, preserves their common exact coordinate, and is
routed to the named local `X1` result. Consequently an active unmatched full
unit cannot be silently discarded.

The milestone is checked by:

```text
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalBN5FullShadowLocalizationAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalBN5FullShadowLocalization.lean
node --test audits/lean-residual-terminal-bn5-full-shadow-localization0.test.mjs
```

The 40-declaration transcript permits only the Lean standard axioms `propext`
and `Quot.sound`. It rejects `Classical.choice`, `sorryAx`, project axioms,
assumption declarations, caller-supplied matching certificates, weakened
coordinates, and weakened deficit or cut-activity checks.

## Exact boundary

This is not the full historical BN5 theorem. Payloads and the quotient-shadow
universe are explicit finite inputs rather than objects derived from the
four-corner bases. Complete shadow matching is not connected back to a BN4
contradiction. The full CritC/Q/E/L/X2/X3/X4 diagnosis, PkgC, BN6, global
routes and selectors, polynomial generation and runtime, ZeroSlack, PCCMin,
SAT in P, and P = NP remain unproved.
