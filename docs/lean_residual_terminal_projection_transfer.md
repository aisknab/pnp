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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-05-102` records 24,150 declarations,
13,019 theorem-kind declarations, 6,918 assumption-free theorem-kind
declarations, 14,409 excluded private declarations, 216 source-closure
modules, and 2,166 reviewed milestone candidates. Its 13,833,685 canonical
bytes have SHA-256
`869875ff563e3aedad0f2b24d241ff91c7c6eb3f35b4ac655346b6f237041188`;
the reviewed Lean source closure has SHA-256
`dd6fd7a05cce2c156ce9196a3c60814a9a220d3d8d0e753e2bcd75d184b2184b`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-05-102` contains 81 milestones: 77
earned and three deliberately unearned. Its 704,920 bytes pin 2,166 exact
kernel theorem types and have SHA-256
`89fbdf1ba505549c8f2f0db99bdc4b6a53895c2a65b094415c7d03dfb0601c4c`.
The generated 1,735,904-byte status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-102` has SHA-256
`4afb84f20713eec92dce2c9c9a0dcaa2f986e893d527d5e1932c41377c73bdc9`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

The canonical non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-102`. Its 186,475-byte
TeX source has SHA-256
`5cc640d457bd64d61c842c2b89bd164052b7cd5a4b123409d821018fac46b396`;
the deterministic 73-page, 429,037-byte A4 PDF has SHA-256
`d4aceaca58c7554027b1c9424da90548c1310dacec77d4074861569b32298938`.

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
