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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-101` records 24,054 declarations,
12,985 theorem-kind declarations, 6,903 assumption-free theorem-kind
declarations, 14,317 excluded private declarations, 216 source modules, and
2,152 reviewed milestone candidates. Its byte-identical status/public copies
have SHA-256
`58d8118f3aef8976a3f1bdb2063a6d08baa7f2fe01e7393881fc9776f738aac9`.
The reviewed Lean source closure is
`5cb2ae9d032d09c08f34424ccdf0b67452d75b8a933b60114c5267cc69385a7f`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-101` contains 81 milestones: 77
earned and three deliberately unearned global milestones. The generated status
coordinate is `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-101`; it retains all
four project assumptions, all six blockers, unset activation fingerprints, an
absent `PNP.Main.p_eq_np`, and a false concrete publication gate.

The canonical non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-101`. Its deterministic
73-page PDF is 428,831 bytes with SHA-256
`654dc634d86e7ebf2633c4d7d67d4cbf36a10c57bede51b4f8cf246fd169fefb`;
the 185,272-byte generated TeX has SHA-256
`f1d9b3f85b0ee7414ab9e40a9e1095f153f208ab9e121f5fd8aa3efef46d7c4a`.
