# Lean terminal executable and physical support completion

`lean/PNP/ResidualTerminalExecutableSaturation.lean` and
`lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean` reconstruct one
bounded dependency edge from §§2–3 of the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`. Section 2 fixes the
directed-circuit carrier conventions; §3 introduces the saturated support
calculus. At this boundary the relevant physical object is the triple
`(U, ∂U, ιU)`: selected gates, incoming boundary wires, and outgoing interface
wires.

## Plain-language result

A finite circuit is a collection of simple Boolean operations connected by
wires. Given any selected collection of its gates, Lean can now identify every
wire that crosses into that collection and every wire that crosses out. The
answer is canonical: duplicate or scrambled starting records do not change it,
and the same circuit always produces the same ordering.

Lean proves both sides of the result. Every real crossing wire is present, and
every listed wire really crosses the selected boundary. Constants stay inside,
wires joining two selected gates stay inside, and only externally visible gate
outputs enter the outgoing interface. In short, no crossing wire is omitted
and no unrelated wire is added.

## Executable saturation

The preceding `ResidualTerminalSaturation` module specified closure
inductively. This milestone adds a deterministic finite work list over the
canonical finite primitive-record universe. It starts from a deduplicated seed,
processes dependencies in canonical order, and uses exactly the size of the
finite universe as fuel. The output is not merely sound: for every terminal
dependency system and finite seed list,
`mem_terminalSaturateRecords_iff` proves membership exactly equivalent to the
inductive `terminalSaturate` relation.

The ten manuscript rule kinds are enumerated directly. The edge decider is
proved equivalent to the relation it decides. The resulting list contains the
seed, contains only inductively reachable records, and is closed under all
declared dependency edges. Duplicate and permuted seeds normalize to the same
canonical output, and cycles terminate without a caller-supplied certificate
or host-side schedule lookup.

## Physical completion in the actual program

For every actual direct-wire program and selected gate-record list, the module
enumerates a finite wire carrier:

- one wire for each program input; and
- one wire for each gate output.

Constants are source terms, not physical crossing wires. A gate source belongs
to the incoming boundary `∂U` exactly when its consumer is selected and its
input or producing gate lies outside `U`. A selected gate belongs to the
outgoing interface `ιU` exactly when its output is consumed by an unselected
gate or is named by the program's output list. Wires whose producer and
consumer are both in `U` remain internal.

`completeTerminalPhysicalSupport_incoming_complete` and
`completeTerminalPhysicalSupport_outgoing_complete` prove those descriptions
universally. `completeTerminalPhysicalSupport_compatible` packages them as the
physical support compatibility invariant. The combined
`completeSaturatedTerminalPhysicalSupport` first executes the finite
saturation and then performs the physical completion, retaining exact record
and compatibility theorems.

This is one construction over all finite direct-wire candidates, explicit
terminal dependency systems, and finite seed lists. The concrete regression
circuits are tests of the universal definitions; they are not hard-coded
milestone coordinates.

## Regression and axiom boundary

The regression covers empty and duplicated seeds, scrambled normalization,
multi-step reachability, unrelated records, an explicit cycle, empty and full
gate selections, a nontrivial middle-gate selection, exact incoming and
outgoing lists, constants, internal wires, and the composed executable result.

All 35 public declarations are listed exactly once in
`lean-audit/PNPResidualTerminalPhysicalSupportCompletionAxiomAudit.lean`. The
compiled closure permits only the approved Lean-standard closure actually
reported by the kernel (`propext` and `Quot.sound`, or no axioms). The hostile
audit rejects project axioms, `Classical.choice`, `sorry`, `admit`, native or
SAT shortcuts, host lookup, caller certificates, missing rule kinds, changed
fuel, duplicate-frontier processing, altered wire predicates, constants as
wires, incomplete crossings, extra declarations, and downstream overclaims.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPhysicalSupportCompletionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPhysicalSupportCompletion.lean
node --test audits/lean-residual-terminal-physical-support-completion0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-05-102` records
24,150 declarations, 13,019 theorem-kind declarations, 6,918 assumption-free
theorems, 14,409 excluded private declarations, 218 source-closure modules,
and 2,166 reviewed milestone candidates. Its 13,833,685 canonical bytes have
SHA-256
`869875ff563e3aedad0f2b24d241ff91c7c6eb3f35b4ac655346b6f237041188`;
the exact Lean source closure has SHA-256
`dd6fd7a05cce2c156ce9196a3c60814a9a220d3d8d0e753e2bcd75d184b2184b`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-05-102`
contains 82 milestones: 79 earned and three deliberately unearned. Its
704,920 bytes pin 2,166 exact kernel theorem types, including all 14 theorem
pins for this milestone, and have SHA-256
`89fbdf1ba505549c8f2f0db99bdc4b6a53895c2a65b094415c7d03dfb0601c4c`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-102`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-05-RESIDUAL-TERMINAL-PHYSICAL-SUPPORT-COMPLETION-101`,
is 1,735,904 bytes with SHA-256
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

The terminal dependency system is still explicit data. This milestone does
not extract the manuscript's complete profile frontier from an arbitrary
circuit, construct proper positive support, or prove support completion in the
manuscript's full governed sense. It does not prove square legitimacy, build
the required projection square, or establish `SaturatePositive`. Package E,
BCEL/BN2–BN6, complete residual routing, ZeroSlack, PCCMin, polynomial runtime,
SAT in P, removal of any project assumption, and `P = NP` all remain open.

The next legitimate milestone must close the named proper-support/square edge
on the path to `SaturatePositive`; repeating another fixed gate coordinate or
finite trace would be regression coverage rather than theorem progress.
