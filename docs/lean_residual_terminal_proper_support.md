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
733,234 bytes pin 2,263 exact kernel theorem types, including all 22 theorem
pins for this milestone, and have SHA-256
`84fe388d393239530a12a76cf14a262c1fdf35e2e1089ced0e90e981aa1c8f09`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-107`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-FRONTIER-PUSHOUT-106`,
is 1,816,951 bytes with SHA-256
`b793312d1177ceaaadb41dda0adafc9c3c5735ed0f19a2b74050faedd97e0685`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-107` has a 192,373-byte
TeX source with SHA-256
`6536c56f5fa0f8c0c8141f214b7f040f2f942b82748652084a5d9ebbafaef435`
and a deterministic 76-page, 434,167-byte A4 PDF with SHA-256
`2bdea0fd4e18e25d08a7b66cf30820d8db83893cc4ab50e14cc8bbcd30b1a264`.

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
