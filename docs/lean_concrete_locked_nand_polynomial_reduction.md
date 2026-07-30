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
semantic compiler now identifies CNFSAT with `EncodedNANDSAT`, but does not
yet supply a finite-machine or polynomial-time reduction witness for that
translation. This milestone does not identify the concrete target with the
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
`PNP-LEAN-THEOREM-INVENTORY-2026-07-31-93` records 21,020 declarations,
11,477 theorems, 5,987 assumption-free theorems, 11,970 excluded private
declarations, 186 source-closure modules, and 2,053 reviewed milestone
candidates. Its 12,933,372 canonical bytes have SHA-256
`576816bd782378cd1d19ad1de76485b82896e6f141853946b6e0ad7df1fefa82`.
The exact Lean source closure has SHA-256
`daed8c40eb6416b42d6b78d87b118b8033bbb5f3e857874c3d1ee45cf89e8876`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-07-31-93` contains 73 milestones: 69
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,053 theorem types; its 671,083 bytes have SHA-256
`c821adfcb65b9bce9c894b5debf99b9ba661457d865e9fed4ecedfd5ff3db88b`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-31-93`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-07-31-CNF-TO-NAND-SEMANTIC-COMPILER-92`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,646,904 bytes have SHA-256
`1fa05f578f1291018c07f3fea452ff970c5bb00950f9382f13956358c94e17ae`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-31-93` has a
171,476-byte TeX source with SHA-256
`505442a00b5b3ebf40a173ee22faf86bc0eb6a12a921899a670a23fc54c6e67d`
and a deterministic 67-page, 415,380-byte A4 PDF with SHA-256
`e042bd2d3263b541adb57295c925aaef4ef38fef7b4cfe7d192d45f772593e49`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
