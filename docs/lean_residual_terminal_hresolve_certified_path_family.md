# Terminal HResolve certified-path family

`lean/PNP/ResidualTerminalHResolveCertifiedPathFamily.lean` composes the
bounded HResolve H-disjoint-family selector with the bounded HN/BWL
certified-path minimum. Every supplied hereditary candidate carries its own
eight-domain footprint, expected frontier, nonempty finite certified-path
family, governed predicate, family-completeness proof, and proof that every
listed path realizes the candidate's support and frontier.

`terminalHResolveGreedyCertifiedPathFamily` processes an arbitrary finite
family from the tail. It retains a candidate exactly when the existing
executable footprint checker proves that candidate H-disjoint from every
already selected candidate. Lean proves the result is a subset of the input,
duplicate-free when the input is duplicate-free, pairwise H-disjoint, and
maximal. Every rejected supplied candidate names a selected blocker and the
first exact support, frontier, origin, kernel, obligation, prefix-tail, charge,
or interface interference route.

For every selected candidate, `minimum?` delegates to the existing exact
four-coordinate BWL selector. The resulting path is listed and lower-bounds
every governed alternative through the candidate's explicit completeness
proof. Its semantic equivalence, expected frontier, nonempty block coverage,
hereditary shape, and support/frontier footprint coherence are preserved.

The named endpoint is
`PNP.DirectWire.terminal_hresolve_certified_path_family_complete`. Its proof is
generic in family length and all eight footprint coordinate types. The
regression selects two mutually H-disjoint candidates, rejects a third through
an exact support collision, and computes a nontrivial minimum for one selected
candidate.

## Evidence

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHResolveCertifiedPathFamilyAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHResolveCertifiedPathFamily.lean
node --test audits/lean-residual-terminal-hresolve-certified-path-family0.test.mjs
```

The axiom transcript covers every public declaration in source order. The
hostile audit rejects missing path-to-footprint coherence, replacement of the
computed minimum or H-disjoint checker, caller-supplied acceptance, erased
maximality or blocker routes, fixed family bounds, assumptions, and widened
claims.

## Boundary

The candidates, paths, footprints, governed predicates, completeness proofs,
and coherence proofs remain supplied. This result does not derive accepted HN
paths or footprints from a terminal candidate, prove HN grammar soundness or
completeness, LN confluence, ParseOrExit, independent leaf tightness, the
H0-H4 `NoHereditary` sidecar, or blocker-to-HB rank semantics. It is not full
or polynomial HResolve, the complete no-lower ledger, unconditional ZeroSlack,
PCCMin, a polynomial-runtime result, SAT in P, or `P = NP`.
