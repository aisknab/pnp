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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-09-118` records 25,863 declarations,
13,665 theorems, 7,079 assumption-free theorems, 14,904 excluded private
declarations, 235 source-closure modules, and 2,449 reviewed milestone
candidates. Its 16,915,940 canonical bytes have SHA-256
`53768f488ff27bf9e43b5b195daaf263fcdcf60e05651d403af23d9a65ff3d78`.
The exact Lean source closure has SHA-256
`bbede19553a26c6ac1b7075cc22f5fb05662056351406e36183a7a734d32d3d9`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-09-118` contains 98 milestones: 95
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,449 theorem types; its 793,613 bytes have SHA-256
`9cc215a43b6c50be85f32a313eed36aca73bc332db9ea4faa21def8659c28f28`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-09-118`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-09-CANDIDATE-SATURATION-COST-BALANCE-117`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,995,750 bytes have SHA-256
`011cb1ee5f5cfe8c1e36b1c3cda6c43638bd22ec27969f2274336e70771052ab`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-09-118` has a
205,214-byte TeX source with SHA-256
`1f59114cfa985649dd1d625dcf13b6dddc6aba47e58aba101dd8197668727ef5`
and a deterministic 80-page, 443,687-byte A4 PDF with SHA-256
`6a1c209fabb6e2d068cba8959ce83e2080af1060a3d07b412a9cf9f68ff29eb7`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
