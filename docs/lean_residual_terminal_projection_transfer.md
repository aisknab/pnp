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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-100` records 23,884 declarations,
12,925 theorem-kind declarations, 6,851 assumption-free theorem-kind
declarations, 14,317 excluded private declarations, 215 source-closure
modules, and 2,145 reviewed milestone candidates. Its 13,702,270 canonical
bytes have SHA-256
`6807fe409ff302b55bffe69f3f7a13c4f0692c297504c9a9ab50692dc57e601e`;
the reviewed Lean source closure has SHA-256
`6a6617e881fca16a46ac1fcb3c5f0968e35cee759596bdbb537d098c6ba24e10`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-100` contains 80 milestones: 77
earned and three deliberately unearned. Its 698,849 bytes pin 2,145 exact
kernel theorem types and have SHA-256
`258f841262220fb0d78db65d35a99809ac2898aed961ba7593dfeadccb6fda54`.
The generated 1,718,803-byte status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-100` has SHA-256
`fa627d391af8be33015576f7b091c32d184cfebe25c708df38f0c6207a313b50`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

The canonical non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-100`. Its 184,334-byte
TeX source has SHA-256
`4b1f709d9bc591832962253a3bc52bec0d8548ea0b0da4a745f4602d04c27aae`;
the deterministic 72-page, 427,894-byte A4 PDF has SHA-256
`da6c2ef9919aef7901253e477a3889808bc6496a79966566e7831bafda5d1b2f`.

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
