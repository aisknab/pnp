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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-98` contains 23,819 declarations,
12,894 theorems, 6,846 assumption-free theorems, four project axioms, and 213
source-closure modules. Its canonical bytes have SHA-256
`82d2b3ec7446b39e9387f8cd24c50e6e6123e4de78aa20c375dd7e34ca16643c`;
the source closure is
`d7b361d14706fa7194432f6e8510a20221ce1f2795064aea153171f19e31efa1`.

`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-98` contains 78 milestones: 75
earned and three intentionally unearned, plus 2,127 exact kernel-type pins.
The current non-claiming report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-98`. Its 182,263-byte
TeX has SHA-256
`1bb780ed9d8c80c906ca9631dd7d2f72a14ca2d1a73f1a773fafdaafea6b1e4f`;
the deterministic 71-page, 425,924-byte A4 PDF has SHA-256
`42ef88a63781e6e56fe43c99574926f85b67a30a524439c65b023f39e79570ef`.

## Exact non-claims

This milestone formalizes only the terminal finite-profile projection and
quotient-to-full firewall. It does not define proper or governed support
carriers, arbitrary quotient coarsening, full or quotient support minima,
projection defect, saturation or completion, Package E, `SaturatePositive`,
`BCELReady`, BN2–BN6, selector completeness, `ZeroSlack`, `PCCMin`, a
polynomial residual route, CNF-SAT in P, or `P = NP`.
