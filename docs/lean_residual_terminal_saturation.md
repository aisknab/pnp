# Lean terminal saturation closure

`lean/PNP/ResidualTerminalSaturation.lean` reconstructs the general closure
operator in §3, “Saturated support calculus and square closure,” of the
canonical manuscript pinned by `archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.  The named manuscript
result is “Saturation closure.”

## What is now kernel-checked

The module defines one finite primitive-record universe for any natural input,
gate, output, and profile widths.  Its four record families are physical gate
coordinates, incoming boundary coordinates, outgoing interface coordinates,
and computed profile coordinates.  The canonical enumeration contains every
record, including when one or more families are empty.

A `TerminalSaturationSystem` carries the already checked computed terminal
profile observer and an explicit Boolean dependency relation.  Each dependency
is tagged by exactly one of the ten mechanisms named by the manuscript:

- gate source;
- interface consumer;
- origin;
- kernel;
- obligation;
- prefix/tail;
- budget;
- saturation;
- direction; and
- charge.

An edge is oriented from an included record to a record that it requires.  The
relation is data at this boundary; it is not a caller-supplied proof that the
dependencies were extracted correctly from an arbitrary circuit.

For every such finite system and every raw support, `terminalSaturate` is the
reflexive transitive closure of those edges.  Lean proves universally that the
result:

- contains the seed support;
- is closed under every governed dependency;
- is the least closed support containing the seed;
- is monotone in the seed;
- is idempotent; and
- is a fixed point exactly when the support is closed.

`saturateSupport` packages the canonical fixed point.  This is one theorem over
all finite carrier widths and all explicit dependency systems, not a sequence
of hard-coded tape positions or example circuits.

## Regression and trust boundary

The regression uses all ten rule tags in a single ten-edge path, so a
one-step-only implementation cannot pass.  It also checks seed inclusion,
monotonicity, idempotence, closure, an unrelated record that remains absent,
an empty primitive universe, membership from all four record families, and a
two-record dependency cycle.

All 18 public declarations are listed exactly once in
`lean-audit/PNPResidualTerminalSaturationAxiomAudit.lean`.  The source and
compiled audits reject project axioms, `Classical.choice`, `sorry`, `admit`,
native or SAT shortcuts, host-side lookup, caller certificates, a reversed
dependency orientation, a missing seed case, a one-step-only closure, a
changed rule family, and downstream overclaims.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSaturationAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSaturation.lean
node --test audits/lean-residual-terminal-saturation0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-05-102` records
24,150 declarations, 13,019 theorem-kind declarations, 6,918 assumption-free
theorems, 14,409 excluded private declarations, 218 source-closure modules,
and 2,166 reviewed milestone candidates.  Its 13,833,685 canonical bytes have
SHA-256
`869875ff563e3aedad0f2b24d241ff91c7c6eb3f35b4ac655346b6f237041188`;
the exact Lean source closure has SHA-256
`dd6fd7a05cce2c156ce9196a3c60814a9a220d3d8d0e753e2bcd75d184b2184b`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-05-102`
contains 82 milestones: 79 earned and three deliberately unearned.  Its
704,920 bytes pin 2,166 exact kernel theorem types, including the seven
saturation pins, and have SHA-256
`89fbdf1ba505549c8f2f0db99bdc4b6a53895c2a65b094415c7d03dfb0601c4c`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-102`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-05-RESIDUAL-TERMINAL-PHYSICAL-SUPPORT-COMPLETION-101`, is
1,735,904 bytes with SHA-256
`4afb84f20713eec92dce2c9c9a0dcaa2f986e893d527d5e1932c41377c73bdc9`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-102` has a 186,475-byte
TeX source with SHA-256
`5cc640d457bd64d61c842c2b89bd164052b7cd5a4b123409d821018fac46b396`
and a deterministic 73-page, 429,037-byte A4 PDF with SHA-256
`d4aceaca58c7554027b1c9424da90548c1310dacec77d4074861569b32298938`.

## What remains open

The following physical-completion milestone now supplies an executable finite
work list equivalent to this closure and computes exact incoming/outgoing wire
boundaries for selected gates in the actual program. This closure theorem by
itself does not derive the dependency relation from an arbitrary program. The
combined development still does not construct the manuscript's proper support
in the required positive form, prove support completion in its full sense, establish square
legitimacy or a projection-compatible square, or instantiate the preceding
four-corner transfer theorem.
`SaturatePositive`, Package E, BCEL/BN2–BN6, route completeness, ZeroSlack,
PCCMin, polynomial runtime, SAT in P, and `P = NP` remain open.  The next
mathematical obligation is to construct the manuscript's governed proper
support in the required positive form and use it to establish the required legitimate projection
square; another fixed record or schedule prefix would be regression evidence
rather than progress on that obligation. See
[`lean_residual_terminal_physical_support_completion.md`](./lean_residual_terminal_physical_support_completion.md).
