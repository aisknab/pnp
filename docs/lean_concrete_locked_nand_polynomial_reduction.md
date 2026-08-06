# Concrete strict-v0 locked-NAND polynomial reduction

## What this milestone establishes

The legacy proof route converts a NAND satisfiability question into a
locked-NAND threshold question. Earlier milestones formalized the exact
strict-version-zero source language, the target encoding, the semantic
equivalence, a total source parser, and a literal target emitter.

This milestone packages those existing results as
`PNP.Concrete.PolynomialReduction`. Its source is `EncodedNANDSAT`, its target
is `EncodedLockedNANDThreshold`, and its function is the already-audited
`strictLockedNANDPolynomialTimeFunction`. For every input bitstring, the
function emits exactly `buildLockedNANDInstance`, and source membership is
equivalent to target membership of that output.

The reduction retains the recursive `FunctionProgram.RawRefinement` witness
for the strict parser/emitter composition. It therefore uses the concrete
finite charged-pipeline model rather than a caller certificate or host-side
schedule.

## Legacy anchor and strategic boundary

The construction follows the locked-NAND SAT embedding and locked-NAND
threshold route in the canonical legacy manuscript pinned by
`archive/legacy-v0/ARCHIVE.json`. Lean remains the theorem authority: the
legacy report supplies the intended construction and dependency order.

This closes the concrete polynomial-reduction packaging edge. The downstream
CNF-to-NAND milestone now identifies CNFSAT with `EncodedNANDSAT` through a
fixed finite machine, a polynomial-time function, and a direct polynomial
reduction, then composes that reduction with this one. This milestone does not
identify the concrete target with the
abstract `PNP.LockedNANDThreshold` language, prove the report-level
`PNP.Main.locked_nand_threshold`, establish CNFSAT NP-hardness or membership
in P, finish ZeroSlack/PCCMin, or prove P = NP.

## Public interface

The public module
`lean/PNP/Concrete/LockedNANDPolynomialReduction.lean` exposes:

- `strictLockedNANDPolynomialReduction`;
- exact function and output theorems;
- exact source/target language equivalence;
- `encodedNANDSAT_reducesTo_encodedLockedNANDThreshold`; and
- preservation of recursive raw refinement.

The focused verification commands are:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDPolynomialReductionAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDPolynomialReduction.lean
node --test \
  audits/lean-concrete-locked-nand-polynomial-reduction0.test.mjs
```

## Mechanically generated publication evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-06-107` records 24,464 declarations,
13,166 theorems, 6,953 assumption-free theorems, 14,594 excluded private
declarations, 223 source-closure modules, and 2,263 reviewed milestone
candidates. Its 14,824,236 canonical bytes have SHA-256
`7e0e7feb895f6ea1c677314b1c2bd8b2ec5f33e826219b0421301e198984720e`.
The exact Lean source closure has SHA-256
`4f08c63941db8fd92e7a33e8f16f698929247d968ae6fce45f4406f8e0aa02fb`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-06-107` contains 87 milestones: 84
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,263 theorem types; its 733,234 bytes have SHA-256
`84fe388d393239530a12a76cf14a262c1fdf35e2e1089ced0e90e981aa1c8f09`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-107`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-FRONTIER-PUSHOUT-106`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,816,951 bytes have SHA-256
`b793312d1177ceaaadb41dda0adafc9c3c5735ed0f19a2b74050faedd97e0685`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-107` has a
192,373-byte TeX source with SHA-256
`6536c56f5fa0f8c0c8141f214b7f040f2f942b82748652084a5d9ebbafaef435`
and a deterministic 76-page, 434,167-byte A4 PDF with SHA-256
`2bdea0fd4e18e25d08a7b66cf30820d8db83893cc4ab50e14cc8bbcd30b1a264`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
