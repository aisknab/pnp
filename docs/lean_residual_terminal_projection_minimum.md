# Lean terminal projection minima

`lean/PNP/ResidualTerminalProjectionMinimum.lean` reconstructs the next
bounded dependency edge after the terminal quotient/full mode firewall. Its
legacy anchor is §5.1, “Projection Monotonicity,” in the canonical manuscript
pinned by `archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

## What is now kernel-checked

For every finite direct-wire implementation, every computed finite terminal
profile system, and every explicit forgetful projection, the module defines
two executable reference searches:

- the **full-profile minimum** scans semantically equivalent candidates that
  agree at every computed profile coordinate;
- the **quotient-profile minimum** scans the same finite candidate space but
  checks only coordinates retained by the projection.

Both scans use the existing complete `allCandidates` enumerator at each exact
gate count from zero through the current gate count of the implementation. The
current implementation always supplies a match, so the total definitions’
fallback branches are proved unreachable. The construction therefore returns
an attained implementation in each mode and proves a universal lower bound
against every other matching realization, including candidates with gate
counts beyond the finite scan bound.

`terminalProjectionMinimum_mono` proves the manuscript’s local projection
monotonicity statement: forgetting profile coordinates cannot increase the
minimum. The module then defines

```text
projection defect = full-profile minimum − quotient-profile minimum
```

and proves the exact additive decomposition. Zero projection defect is
equivalent both to equality of the two minima and to the existence of an
attained quotient-minimum comparison carrying the mode firewall’s checked full
lift. Conversely, positive defect rules out such a lift at every attained
quotient minimum. A projection that keeps every coordinate has equal minima.

These statements quantify over the unbounded family of finite direct-wire
implementations and profile systems. The one-gate redundant-identity example
is only a regression: forgetting its gate-presence coordinate produces full
minimum one, quotient minimum zero, and projection defect one.

## Trust and verification boundary

The implementation is constructive and finite. It does not use
`Classical.choice`, `sorry`, `admit`, `native_decide`, host-side lookup, a
caller-supplied minimum certificate, or any project axiom. The 27 public
declarations are listed exactly once in
`lean-audit/PNPResidualTerminalProjectionMinimumAxiomAudit.lean`; their
compiled closure uses only the approved Lean-standard `propext` dependency
where required.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProjectionMinimumAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProjectionMinimum.lean
node --test audits/lean-residual-terminal-projection-minimum0.test.mjs
```

The regression covers zero-width profiles, lossless and forget-all
projections, attained full and quotient minima, semantic equivalence at both
Boolean input values, universal lower bounds, monotonicity, exact defect one,
and the positive-defect lifting firewall. The hostile audit rejects incomplete
enumeration, coordinate omission or inversion, a weakened full matcher,
swapped minima, reversed defect subtraction, a false lifting step, hidden
assumptions, project axioms, host evaluation, caller certificates, and global
overclaims.

## What remains open

This is an exhaustive reference construction, not a polynomial algorithm. It
does not yet construct the manuscript’s proper support or governed carrier,
prove `SaturatePositive`, establish Package E or BCEL/BN2–BN6, generate a
complete residual route, prove ZeroSlack, complete PCCMin, decide SAT in
polynomial time, prove polynomial runtime for this search, discharge any of
the four project assumptions, or prove
`P = NP`.

The next mathematical obligation is therefore not another fixed profile or
coordinate. It is the manuscript-grounded unbounded proper-support/saturation
edge that can feed these now-formalized minima into the later transfer and
BCEL obligations.

## Generated publication evidence

The compiled inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-99` records 23,855 declarations,
12,917 theorem-kind declarations, 6,849 assumption-free theorem-kind
declarations, 14,316 excluded private declarations, 214 source modules, and
2,141 reviewed milestone candidates. Its byte-identical status/public copies
have SHA-256
`7c3daaa3cbf191508d48054ecf1d1b48cfbd7601d5e3756fa9d057db383c6121`.
The reviewed Lean source closure is
`7a2758acc431c096d32534b9b0860fdf996b27a5f3def918e131dd10c1b99006`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-99` contains 79 milestones: 76
earned and three deliberately unearned global milestones. The generated status
coordinate is `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-99`; it retains all
four project assumptions, all six blockers, unset activation fingerprints, an
absent `PNP.Main.p_eq_np`, and a false concrete publication gate.

The canonical non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-99`. Its deterministic
72-page PDF is 427,318 bytes with SHA-256
`cd354d1406f9cfa3374ebf716cfc401261bb9905bc573fc3c0d6368e7ca1f0ad`;
the 183,404-byte generated TeX has SHA-256
`8af67370cfd1b95708f30da4009dfdb04f5ab8793db81ae1987c411982f1b869`.
