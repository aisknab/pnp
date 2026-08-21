# Terminal HN BWL certified-path minimum

`lean/PNP/ResidualTerminalHNBWLCertifiedPathMinimum.lean` formalizes the exact
finite minimization kernel used after hereditary paths have already been
certified. Each path carries one of the manuscript's pair, tripod, spine, or
non-flat shape tags, a nonempty block decomposition covering its support, a
direct-wire implementation with complete semantic-equivalence evidence, and
an exact expected-frontier equality.

`TerminalHNBWLCertifiedPath.objective` derives the cost coordinate from the
carried implementation's gate count. The remaining residual-rank,
frontier-deviation, and direct-wire-code coordinates are stored in the path.
`TerminalHNBWLObjective.LexLE` compares those four coordinates in that exact
priority order, and `checkLexLE` is proved equivalent to the proposition.

`terminalHNBWLMinimum?` recursively computes a deterministic minimum of any
nonempty finite supplied path family. Lean proves that the selected path is a
member of that family and that its objective is no greater than every listed
alternative. The named endpoint,
`PNP.DirectWire.terminal_hn_bwl_certified_path_minimum_complete`, accepts a
separate explicit proof that the supplied family covers a governed predicate.
It then lifts the lower bound to every governed path and returns the selected
path's semantic, frontier, block, and shape evidence.

## Evidence

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHNBWLCertifiedPathMinimumAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHNBWLCertifiedPathMinimum.lean
node --test audits/lean-residual-terminal-hn-bwl-certified-path-minimum0.test.mjs
```

The axiom transcript covers every public declaration in source order. The
regression exercises all four shape tags and each objective priority. The
hostile audit rejects caller-supplied cost or success, omitted objective or
certificate coordinates, weakened membership, hidden completeness, fixed
family bounds, assumptions, and widened claims.

## Boundary

The certified path family, governed predicate, and any completeness proof are
supplied. This result does not derive paths from terminal data, prove the
shape-specific grammar sound or complete, establish LN confluence,
ParseOrExit, independent leaf tightness, or the full BWL theorem, or construct
a polynomial path generator or runtime. It does not complete HResolve, the
H0-H4 `NoHereditary` sidecar, the complete no-lower ledger, unconditional
ZeroSlack, PCCMin, concrete SAT, the root theorem, or project-axiom removal.
