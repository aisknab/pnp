# Terminal quotient/full mode firewall

`lean/PNP/ResidualTerminalModeFirewall.lean` reconstructs the finite-profile
mode firewall from §§5.1–5.2 of the pinned legacy report and the
`quotientEqualityNotConstructive` field of the terminal `RW-MuBridge` audit in
Theorem 10.1.
It extends the preceding whole-semantics bridge without changing its NAND
semantics or gate-count convention.

## Full profiles and quotient comparison

The manuscript's full profile has ten roles: carrier, origin, kernel,
obligation, prefix, direction, saturation, budget, charge, and frontier. The
Lean module represents their finite data by role-indexed Boolean coordinates.
A `TerminalProfileSystem` computes those coordinates from the actual
`Implementation`; it has no trusted `projectionSound`, `fullLiftComplete`, or
similar caller flag.

A `TerminalFullCarrierRealization` contains the existing complete
`TerminalFullRealization` and agrees with the current implementation at every
profile coordinate. A `TerminalProfileProjection` marks coordinates as kept or
forgotten. Its `TerminalQuotientComparison` still agrees on every Boolean input
and output, but compares only the kept profile coordinates.

Projection retains the exact implementation, program, gate count, and complete
multi-output semantics. Profile data never becomes a free Boolean input or
output.

## Checked lifting and the firewall

`TerminalCheckedFullLift` requires exact agreement at every forgotten
coordinate. Lean proves that such a lift exists exactly when the candidate's
complete profile agrees with the target. A projection that keeps every
coordinate lifts automatically. If the target's obligation coordinates are
discharged, both a full realization and a checked lift preserve that fact.

The public theorem

```text
terminalQuotientEqualityNotConstructive
```

states the negative boundary. If a quotient comparison has even one forgotten
coordinate whose computed value differs, no checked full lift exists. The
regression instantiates this universally quantified theorem with two circuits
that compute the same identity function: one contains an unused NAND gate and
one does not. Dropping the computed gate-presence profile bit makes the
quotient comparison pass, but the full profiles differ and constructive
full-carrier promotion is rejected.

This is an information-flow theorem, not a convention enforced only by prose.
It also does not say that the two circuits have different Boolean semantics;
their complete Boolean equivalence is retained deliberately. What is missing
is the full carrier information required by later profile-sensitive residual
rewrites.

## Trust and regression boundary

The axiom transcript covers every explicit public declaration. The hostile
audit fixes the import closure and rejects missing profile coordinates,
implicit defaults, quotient-to-full promotion, reopened obligations, changed
implementations or gate counts, profile data entering Boolean outputs, project
axioms, `Classical.choice`, `sorry`, `admit`, native evaluation, host lookup,
caller certificates, and theorem overclaims.

After building the root target, run:

```bash
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalModeFirewallAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalModeFirewall.lean
node --test audits/lean-residual-terminal-mode-firewall0.test.mjs
```

## Generated publication evidence

The compiled inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-99` contains 23,855 declarations,
12,917 theorems, 6,849 assumption-free theorems, four project axioms, and 214
source-closure modules. Its canonical bytes have SHA-256
`7c3daaa3cbf191508d48054ecf1d1b48cfbd7601d5e3756fa9d057db383c6121`;
the source closure is
`7a2758acc431c096d32534b9b0860fdf996b27a5f3def918e131dd10c1b99006`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-99` contains 79 milestones: 76
earned and three intentionally unearned, plus 2,141 exact kernel-type pins.
The current non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-99`. Its 183,404-byte
TeX has SHA-256
`8af67370cfd1b95708f30da4009dfdb04f5ab8793db81ae1987c411982f1b869`;
the deterministic 72-page, 427,318-byte A4 PDF has SHA-256
`cd354d1406f9cfa3374ebf716cfc401261bb9905bc573fc3c0d6368e7ca1f0ad`.

## Exact non-claims

This milestone formalizes only the terminal finite-profile projection and
quotient-to-full firewall. It does not define proper or governed support
carriers, arbitrary quotient coarsening, full or quotient support minima,
projection defect, saturation or completion, Package E, `SaturatePositive`,
`BCELReady`, BN2–BN6, selector completeness, `ZeroSlack`, `PCCMin`, a
polynomial residual route, CNF-SAT in P, or `P = NP`.
