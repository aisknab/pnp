# Saturated support square closure in Lean

`lean/PNP/ResidualTerminalSupportSquareClosure.lean` reconstructs the
algebraic and physical part of the “Saturated support square closure” theorem
in §3 of the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

The preceding milestones supplied a finite terminal-record universe,
executable saturation for every finite seed, exact physical boundary and
interface completion, and semantic extraction of any selected gate support.
This milestone combines those general constructions for two arbitrary seeds.

## Plain-language result

Take any finite Boolean circuit, an explicit list of dependency rules, and two
starting selections of terminal records. Lean now computes four related
selections:

- everything required by the left starting selection;
- everything required by the right starting selection;
- the records shared by both completed selections; and
- every record belonging to either completed selection.

The shared selection is the largest selection contained in both sides. The
combined selection is the smallest selection containing both sides. Lean
proves that all four selections remain closed under every supplied dependency
rule.

For each of the four selections, Lean also computes the actual circuit wires
that enter and leave the selected gates. It proves that this physical boundary
is complete and extracts a smaller open circuit whose behavior exactly matches
the selected part of the original circuit.

This result applies to every finite direct-wire candidate, every explicit
terminal dependency system, and every pair of finite seeds. It is not a list
of fixed examples or hard-coded support coordinates.

## Technical construction

For a `TerminalSaturationSystem` and two finite seed lists,
`TerminalSaturatedSupportSquare` defines the four corners as follows:

```text
left  = terminalSaturateRecords(system, leftSeed)
right = terminalSaturateRecords(system, rightSeed)
meet  = canonical enumeration of left ∩ right
join  = terminalSaturateRecords(system, left ++ right)
```

The meet filters the canonical finite primitive-record universe, so its list
order is deterministic and its membership theorem is exact. The two side
saturations are already closed. Because every governed dependency has one
dependent and one required record, their union is also closed. The final join
saturation therefore adds no new member, while retaining the existing
executable saturation boundary.

Lean proves:

- exact membership specifications for meet and join;
- dependency closure of all four corners;
- meet is below both sides and is their greatest lower bound;
- join is above both sides and is their least upper bound;
- seed order and duplicate occurrences do not change any corner
  extensionally;
- exact physical incoming-boundary and outgoing-interface compatibility for
  every corner;
- one extracted NAND gate for each selected ambient gate; and
- equality with independent open-support semantics, including recovery on
  boundary values induced by the original whole-circuit execution.

The square therefore supplies the finite meet/join closure and physical
support data needed before the manuscript's later projection-compatible
square obligations can be stated over computed corners.

## Regression and axiom boundary

The regression uses a four-gate direct-wire circuit and all four primitive
record families. Its dependency graph exercises gate-source, origin, charge,
and direction edges. The left and right saturations overlap without being
equal, so the exact meet and join lists are nontrivial. The regression checks
empty and identical seeds, duplicate and reordered multi-record seeds, the
greatest-lower-bound and least-upper-bound laws, all four completed physical
boundaries, extracted gate counts, concrete truth-table values, universal open
semantics, and induced whole-circuit recovery.

The axiom transcript lists all 29 new public declarations and 11 reused
saturation, completion, and extraction interfaces exactly once. The compiled
closure permits only the Lean-standard axioms actually reported by the kernel.
The hostile audit rejects a union substituted for the meet, an unsaturated
join, omitted closure reasoning, caller certificates, host lookup, hard-coded
support families, project axioms, `Classical.choice`, `sorry`, `admit`, native
shortcuts, and downstream overclaims.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSupportSquareClosureAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSupportSquareClosure.lean
node --test audits/lean-residual-terminal-support-square-closure0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-06-107` records
24,464 declarations, 13,166 theorem-kind declarations, 6,953 assumption-free
theorems, 14,594 excluded private declarations, 223 source-closure modules,
and 2,263 reviewed milestone candidates. Its 14,824,236 canonical bytes have
SHA-256
`7e0e7feb895f6ea1c677314b1c2bd8b2ec5f33e826219b0421301e198984720e`;
the exact Lean source closure has SHA-256
`4f08c63941db8fd92e7a33e8f16f698929247d968ae6fce45f4406f8e0aa02fb`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-06-107`
contains 87 milestones: 84 earned and three deliberately unearned. Its
733,234 bytes pin 2,263 exact kernel theorem types, including the 23 theorem
pins for this milestone, and have SHA-256
`84fe388d393239530a12a76cf14a262c1fdf35e2e1089ced0e90e981aa1c8f09`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-107`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-FRONTIER-PUSHOUT-106`,
is 1,816,951 bytes with SHA-256
`b793312d1177ceaaadb41dda0adafc9c3c5735ed0f19a2b74050faedd97e0685`.
It records the square closure, exact meet/join laws, physical compatibility,
semantic extraction, and axiom audit as true while retaining all four project
assumptions, all six blockers, unset activation fingerprints, an absent
`PNP.Main.p_eq_np`, and a false concrete publication gate.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-107` has a 192,373-byte
TeX source with SHA-256
`6536c56f5fa0f8c0c8141f214b7f040f2f942b82748652084a5d9ebbafaef435`
and a deterministic 76-page, 434,167-byte A4 PDF with SHA-256
`2bdea0fd4e18e25d08a7b66cf30820d8db83893cc4ab50e14cc8bbcd30b1a264`.

## What remains open

The terminal dependency system remains explicit caller data. This milestone
does not derive the manuscript's full terminal profile frontier from an
arbitrary circuit. Its automatically computed physical boundary is not a
proof of the manuscript's full governed completion alternative or its named
obstruction routing.

In particular, this is not yet the manuscript's projection-compatible square:
it does not prove the frontier pushout, carrier and profile transport,
projection commutation, side-tight four-corner minima, or BN2 square
legitimacy. It does not prove `SaturatePositive`, Package E, `BCELReady`, any
of BN2 through BN6, complete residual routing, ZeroSlack, PCCMin, polynomial
runtime, SAT in P, removal of a project assumption, or `P = NP`.

The next earned milestone must use these all-finite computed corners to close
a named governed-completion or square-legitimacy dependency. Repeating the
construction at fixed coordinates would be regression evidence, not theorem
progress.
