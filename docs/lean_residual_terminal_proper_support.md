# Lean search for governed proper-positive terminal supports

`lean/PNP/ResidualTerminalProperSupport.lean` reconstructs the next bounded
dependency edge from §2.2, §3, and §10 of the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

The manuscript defines the local gain of a compatible support by

```text
g_C(U) = |U| - mu*(F_C,U).
```

The preceding Lean milestones supplied the finite terminal primitive-record
universe, executable saturation, physical completion, arbitrary support
extraction, exact open semantics, and induced whole-circuit recovery. This
milestone decides which canonical terminal seeds produce a proper support with
positive exact local gain.

## Plain-language result

Suppose a large Boolean circuit contains a smaller collection of gates. The
question is whether those gates can be replaced by a smaller circuit without
changing what that part of the circuit does.

Lean can now perform a complete finite reference search for this situation.
It considers every possible selection of the terminal records, applies every
dependency required by the supplied governance rules, cuts out the resulting
open circuit, and compares its gate count with the exact minimum circuit for
the same inputs and outputs.

A returned result proves all of the following:

- at least one ambient gate was selected;
- not every ambient gate was selected;
- all supplied dependency rules are closed;
- the physical incoming and outgoing wires are compatible;
- the extracted circuit has the exact open behavior of the selected gates;
- the behavior agrees with the original circuit on induced boundary values;
- an equivalent exact-minimum replacement exists; and
- that replacement uses strictly fewer NAND gates.

If the search returns no result, Lean proves that no governed proper-positive
support exists among the canonical seeds. This is stronger than merely
reporting that one particular attempt failed.

## Technical construction

`allTerminalSupportSeeds` enumerates every order-preserving subset of the
finite primitive-record universe. For every Boolean selector,
`canonicalTerminalSupportSeed` filters that universe, and
`canonicalTerminalSupportSeed_mem` proves that the resulting subset occurs in
the enumeration. Thus every Boolean-selected subset has a canonical list
representative. In other words, every Boolean-selected subset occurs in the
search universe.

For each seed, `terminalSupportLocalGain` computes

```text
residualSlack(extractSaturatedTerminalSupport(C, system, seed)).
```

Here the residual slack is the extracted gate count minus the exhaustive
reference minimum for exactly the extracted boundary, ordered interface, and
open Boolean semantics. `TerminalSupportProper` requires the extracted gate
count to be positive and strictly below the ambient gate count.
`TerminalSupportPositive` requires the exact local gain to be positive.

`findTerminalProperPositiveSupport` scans the complete canonical seed list in
deterministic order. Its result is a `TerminalProperPositiveSupport` carrying
the seed and proofs of governance, properness, and positivity. The soundness
theorem exposes those proofs. The completeness theorem shows that any
qualifying canonical seed makes the search succeed. The exact negative theorem
states that the search returns `none` exactly when no governed proper-positive
support with positive local gain exists among the canonical seeds:

```text
findTerminalProperPositiveSupport C system = none
iff
every canonical seed is not both proper and positive.
```

The returned support reuses the existing kernel-checked closure,
compatibility, semantics, and induced-recovery theorems. Its
`minimumReplacement` is the exhaustive reference-minimum candidate for the
same open function. Positive local gain proves that replacement is strictly
smaller.

## Regression and axiom boundary

The regression uses a general three-gate direct-wire circuit. Its selected
two-gate double negation computes a direct boundary projection, so the exact
open minimum has zero gates and the local gain is two. It checks all 32 seeds
of the five-record universe, canonical selector coverage, exact boundaries and
interface, both boundary valuations, deterministic first-result behavior,
strict minimum replacement, and the negative one-gate case where no nonempty
proper support can exist.

The axiom transcript covers all 26 new public declarations and 11 reused
saturation, extraction, compatibility, and minimum-replacement interfaces.
The compiled closure permits only the Lean-standard axioms actually reported
by the kernel: `propext`, `Quot.sound`, or no axioms. The hostile audit rejects
incomplete seed enumeration, skipped saturation, non-strict properness,
nonpositive gain, incomplete search, weakened negative specifications,
caller certificates, host lookup, hard-coded support families, project axioms,
`Classical.choice`, `sorry`, `admit`, native shortcuts, and downstream
overclaims.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProperSupportAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProperSupport.lean
node --test audits/lean-residual-terminal-proper-support0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-06-106` records
24,405 declarations, 13,134 theorem-kind declarations, 6,945 assumption-free
theorems, 14,576 excluded private declarations, 222 source-closure modules,
and 2,240 reviewed milestone candidates. Its 14,564,176 canonical bytes have
SHA-256
`38c53b1e3e80059332ff62f135ffebcf04d6b5e39e158f0f48965295894c6e8d`;
the exact Lean source closure has SHA-256
`b4be2de72b2909cd9e47f0748e061f03041fbecbac1360e5797e89fef18404f6`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-06-106`
contains 86 milestones: 83 earned and three deliberately unearned. Its
726,779 bytes pin 2,240 exact kernel theorem types, including all 22 theorem
pins for this milestone, and have SHA-256
`3b27c4f934c3897bb71584846005e93a4816b63f4f8750a6884d18f1aedfe7ce`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-106`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-GOVERNED-SUPPORT-COMPLETION-105`,
is 1,798,304 bytes with SHA-256
`5e6356f2b13da0161b4b0fb0ea299b504bfef54f7670f3a4371d1b19df26d10f`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-106` has a 191,295-byte
TeX source with SHA-256
`1dc4a81c1f7a9805405019d1298f5324aaf39f599a4b58433bf72ceeb97a5a9c`
and a deterministic 75-page, 432,609-byte A4 PDF with SHA-256
`04683262a3cd12a893f7d1d67c750502f52f40a9c8bf7755912b3ebbff76d5fb`.

## What remains open

The terminal dependency system is still explicit data. More precisely, the
construction takes an explicit terminal dependency system from its caller. This milestone does
not derive the manuscript's full profile frontier from an arbitrary circuit or
prove support completion in its full governed sense. It does not prove that a
positive whole-circuit residual witness must yield one of these proper
supports, preserve positivity through every saturation step, construct a
legitimate projection-compatible support square, or establish
`SaturatePositive` or `BCELReady`.

The search is an exhaustive finite reference computation, not a polynomial
algorithm. The remaining square legitimacy obligation, the projection square, Package E, BN2 through
BN6, complete residual routing, ZeroSlack, PCCMin, polynomial runtime, SAT in
P, removal of the four project assumptions, and `P = NP` remain open.

The next earned milestone must close the full governed-completion or
square-legitimacy edge on the finite path to `SaturatePositive`. Repeating a
fixed seed or hard-coded circuit would be regression coverage rather than
theorem progress.
