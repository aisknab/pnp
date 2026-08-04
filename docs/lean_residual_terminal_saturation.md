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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-04-101` records
24,054 declarations, 12,985 theorem-kind declarations, 6,903 assumption-free
theorems, 14,317 excluded private declarations, 216 source-closure modules,
and 2,152 reviewed milestone candidates.  Its 13,748,432 canonical bytes have
SHA-256
`58d8118f3aef8976a3f1bdb2063a6d08baa7f2fe01e7393881fc9776f738aac9`;
the exact Lean source closure has SHA-256
`5cb2ae9d032d09c08f34424ccdf0b67452d75b8a933b60114c5267cc69385a7f`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-04-101`
contains 81 milestones: 78 earned and three deliberately unearned.  Its
701,078 bytes pin 2,152 exact kernel theorem types, including the seven
saturation pins, and have SHA-256
`a86df7f8d45a5430bc1b7cc67dfac31e8663a9e81ed24abc0f25a2cd299b0b7c`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-101`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-04-RESIDUAL-TERMINAL-SATURATION-100`, is
1,725,364 bytes with SHA-256
`ada16fd663a00a8ff6a10ba29693df2b0a13fe3cf6b68ec7521da9259d5de235`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-101` has a 185,272-byte
TeX source with SHA-256
`f1d9b3f85b0ee7414ab9e40a9e1095f153f208ab9e121f5fd8aa3efef46d7c4a`
and a deterministic 73-page, 428,831-byte A4 PDF with SHA-256
`654dc634d86e7ebf2633c4d7d67d4cbf36a10c57bede51b4f8cf246fd169fefb`.

## What remains open

This closure theorem does not derive the dependency relation from an arbitrary
program.  It does not yet construct the manuscript's proper support, prove
support completion, establish square legitimacy or a projection-compatible
square, or instantiate the preceding four-corner transfer theorem.
`SaturatePositive`, Package E, BCEL/BN2–BN6, route completeness, ZeroSlack,
PCCMin, polynomial runtime, SAT in P, and `P = NP` remain open.  The next
mathematical obligation is to connect the manuscript's governed support
construction to this closure operator; another fixed record or schedule prefix
would be regression evidence rather than progress on that obligation.
