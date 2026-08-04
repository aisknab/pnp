# Lean terminal projection transfer identity

`lean/PNP/ResidualTerminalProjectionTransfer.lean` reconstructs the bounded
arithmetic edge in §5.2, “Mode firewall and transfer identity,” of the
canonical manuscript pinned by `archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

## What is now kernel-checked

The module packages four implementations—meet, left, right, and join—that
share one computed terminal-profile system and one explicit projection. It
then defines two four-corner changes:

```text
full delta     = full(left) + full(right) - full(meet) - full(join)
quotient delta = quot(left) + quot(right) - quot(meet) - quot(join)
```

Both values use signed integers. This matters: even though each individual
minimum is a natural number, a four-corner delta can be negative. The
projection excess is the signed difference

```text
Omega = quotient delta - full delta.
```

`terminalProjectionDefect_int` first transports the existing natural
projection defect into the exact signed difference of full and quotient
minima. The proof uses the previously checked projection monotonicity theorem;
it does not silently truncate a negative integer difference back into `Nat`.

`TerminalProjectionFourCorners.transferIdentity` then proves the §5.2 balance
law for every finite family with the shared observer and projection:

```text
defect(join) + defect(meet)
  = defect(left) + defect(right) + Omega.
```

The theorem is purely algebraic once the four defect identities are expanded.
It is nevertheless a useful dependency edge: later support and saturation
work may instantiate one checked identity instead of repeating cast and sign
bookkeeping at every corner.

The constant-cut corollary says that if meet, left, and right have zero defect
and join has defect `D`, then `Omega = D`. A positive `D` therefore gives
positive projection excess. The theorem does not assume that the four corners
already form a legitimate proper-support or saturated square.

## Regression and trust boundary

The regression includes:

- an all-zero family;
- a lossless keep-all projection whose full and quotient deltas are both
  negative;
- a forget-all constant-cut example with full delta `-1`, quotient delta `0`,
  and projection excess `1`;
- the exact transfer and constant-cut equations; and
- concrete left/right symmetry with unequal side implementations.

All eight public declarations are listed exactly once in
`lean-audit/PNPResidualTerminalProjectionTransferAxiomAudit.lean`. The source
and compiled audits reject `Classical.choice`, project axioms, `sorry`,
`admit`, native or SAT shortcuts, host-side lookup, caller certificates,
reversed signs, swapped corner roles, separate projections, and a cast that
does not use proved monotonicity.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProjectionTransferAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProjectionTransfer.lean
node --test audits/lean-residual-terminal-projection-transfer0.test.mjs
```

## Generated publication evidence

The compiled inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-101` records 24,054 declarations,
12,985 theorem-kind declarations, 6,903 assumption-free theorem-kind
declarations, 14,317 excluded private declarations, 216 source-closure
modules, and 2,152 reviewed milestone candidates. Its 13,748,432 canonical
bytes have SHA-256
`58d8118f3aef8976a3f1bdb2063a6d08baa7f2fe01e7393881fc9776f738aac9`;
the reviewed Lean source closure has SHA-256
`5cb2ae9d032d09c08f34424ccdf0b67452d75b8a933b60114c5267cc69385a7f`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-101` contains 81 milestones: 77
earned and three deliberately unearned. Its 701,078 bytes pin 2,152 exact
kernel theorem types and have SHA-256
`a86df7f8d45a5430bc1b7cc67dfac31e8663a9e81ed24abc0f25a2cd299b0b7c`.
The generated 1,725,364-byte status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-101` has SHA-256
`ada16fd663a00a8ff6a10ba29693df2b0a13fe3cf6b68ec7521da9259d5de235`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

The canonical non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-101`. Its 185,272-byte
TeX source has SHA-256
`f1d9b3f85b0ee7414ab9e40a9e1095f153f208ab9e121f5fd8aa3efef46d7c4a`;
the deterministic 73-page, 428,831-byte A4 PDF has SHA-256
`654dc634d86e7ebf2633c4d7d67d4cbf36a10c57bede51b4f8cf246fd169fefb`.

## What remains open

This module proves one unbounded algebraic identity over all finite four-corner
families of the stated shape. It does not construct proper support, prove that
the four corners arise from the manuscript’s governed square, establish
`SaturatePositive`, generate a route, discharge Package E or BCEL/BN2–BN6,
prove ZeroSlack or PCCMin, supply polynomial runtime, decide SAT in polynomial
time, remove any of the four project assumptions, or prove `P = NP`.

The next mathematical obligation is the manuscript-grounded support and
saturation construction that supplies legitimate corners to this identity.
Another hard-coded coordinate or finite example would be regression evidence,
not progress on that obligation.
