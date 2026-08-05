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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-05-102` records 24,150 declarations,
13,019 theorem-kind declarations, 6,918 assumption-free theorem-kind
declarations, 14,409 excluded private declarations, 216 source modules, and
2,166 reviewed milestone candidates. Its byte-identical status/public copies
have SHA-256
`869875ff563e3aedad0f2b24d241ff91c7c6eb3f35b4ac655346b6f237041188`.
The reviewed Lean source closure is
`dd6fd7a05cce2c156ce9196a3c60814a9a220d3d8d0e753e2bcd75d184b2184b`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-05-102` contains 81 milestones: 77
earned and three deliberately unearned global milestones. The generated status
coordinate is `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-102`; it retains all
four project assumptions, all six blockers, unset activation fingerprints, an
absent `PNP.Main.p_eq_np`, and a false concrete publication gate.

The canonical non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-102`. Its deterministic
73-page PDF is 429,037 bytes with SHA-256
`d4aceaca58c7554027b1c9424da90548c1310dacec77d4074861569b32298938`;
the 186,475-byte generated TeX has SHA-256
`5cc640d457bd64d61c842c2b89bd164052b7cd5a4b123409d821018fac46b396`.
